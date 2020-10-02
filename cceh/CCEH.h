#ifndef CCEH_H_
#define CCEH_H_

#include <cstring>
#include <cmath>
#include <vector>
#include <iostream>
#include <cmath>
#include <thread>
#include <bitset>
#include <cassert>
#include <unordered_map>

#include "cceh/pair.h"
#include "cceh/persist.h"
#include "cceh/uhash.h"

#include "index.hpp"

#define INPLACE 1

constexpr size_t kSegmentBits = 8;
constexpr size_t kMask = (1 << kSegmentBits)-1;
constexpr size_t kShift = kSegmentBits;
constexpr size_t kSegmentSize = (1 << kSegmentBits) * 16 * 4;
constexpr size_t kNumPairPerCacheLine = 4;
constexpr size_t kNumCacheLine = 4;

using VKVO = viper::internal::KeyValueOffset;

template <typename KeyT, typename ValueT>
struct Segment {
  static const size_t kNumSlot = kSegmentSize / sizeof(Pair<KeyT, ValueT>);

  Segment(void)
  : local_depth{0}
  { }

  Segment(size_t depth)
  :local_depth{depth}
  { }

  ~Segment(void) {
  }

  void* operator new(size_t size) {
    void* ret;
    posix_memalign(&ret, 64, size);
    return ret;
  }

  void* operator new[](size_t size) {
    void* ret;
    posix_memalign(&ret, 64, size);
    return ret;
  }

  int Insert(KeyT&, ValueT, size_t, size_t);
  void Insert4split(KeyT&, ValueT, size_t);
  Segment** Split(void);

  Pair<KeyT, ValueT> _[kNumSlot];
  size_t local_depth;
  int64_t sema = 0;
  size_t pattern = 0;
  size_t numElem(void); 
};

template <typename KeyT, typename ValueT>
struct Directory {
  static const size_t kDefaultDepth = 10;
  Segment<KeyT, ValueT>** _;
  size_t capacity;
  size_t depth;
  bool lock;
  int sema = 0 ;

  Directory(void) {
    depth = kDefaultDepth;
    capacity = pow(2, depth);
    _ = new Segment<KeyT, ValueT>*[capacity];
    lock = false;
    sema = 0;
  }

  Directory(size_t _depth) {
    depth = _depth;
    capacity = pow(2, depth);
    _ = new Segment<KeyT, ValueT>*[capacity];
    lock = false;
    sema = 0;
  }

  ~Directory(void) {
    delete [] _;
  }

  bool Acquire(void) {
    bool unlocked = false;
    return CAS(&lock, &unlocked, true);
  }

  bool Release(void) {
    bool locked = true;
    return CAS(&lock, &locked, false);
  }
  
  void SanityCheck(void*);
  void LSBUpdate(int, int, int, int, Segment<KeyT, ValueT>**);
};

template <typename KeyT, typename ValueT>
class CCEH {
  public:
    CCEH(void);
    CCEH(size_t);
    ~CCEH(void);
    void Insert(KeyT&, ValueT);
    bool InsertOnly(KeyT&, ValueT);
    bool Delete(KeyT&);
    ValueT Get(KeyT&);
    ValueT FindAnyway(KeyT&);
    double Utilization(void);
    size_t Capacity(void);
    bool Recovery(void);

    void* operator new(size_t size) {
      void *ret;
      posix_memalign(&ret, 64, size);
      return ret;
    }

  private:
    size_t global_depth;
    Directory<KeyT, ValueT>* dir;
};

extern size_t perfCounter;

template <typename K, typename V>
int Segment<K, V>::Insert(K& key, V value, size_t loc, size_t key_hash) {
#ifdef INPLACE
    if (sema == -1) return 2;
  if ((key_hash >> (8*sizeof(key_hash)-local_depth)) != pattern) return 2;
  auto lock = sema;
  int ret = 1;
  while (!CAS(&sema, &lock, lock+1)) {
    lock = sema;
  }
  K LOCK = INVALID;
  for (unsigned i = 0; i < kNumPairPerCacheLine * kNumCacheLine; ++i) {
    auto slot = (loc + i) % kNumSlot;
    auto _key = _[slot].key;
    if ((h(&_[slot].key,sizeof(K)) >> (8*sizeof(key_hash)-local_depth)) != pattern) {
      CAS(&_[slot].key, &_key, INVALID);
    }
    if (CAS(&_[slot].key, &LOCK, SENTINEL)) {
      _[slot].value = value;
      mfence();
      _[slot].key = key;
      ret = 0;
      break;
    } else {
      LOCK = INVALID;
    }
  }
  lock = sema;
  while (!CAS(&sema, &lock, lock-1)) {
    lock = sema;
  }
  return ret;
#else
    if (sema == -1) return 2;
    if ((key_hash >> (8*sizeof(key_hash)-local_depth)) != pattern) return 2;
    auto lock = sema;
    int ret = 1;
    while (!CAS(&sema, &lock, lock+1)) {
        lock = sema;
    }
    K LOCK = INVALID;
    for (unsigned i = 0; i < kNumPairPerCacheLine * kNumCacheLine; ++i) {
        auto slot = (loc + i) % kNumSlot;
        if (CAS(&_[slot].key, &LOCK, SENTINEL)) {
            _[slot].value = value;
            mfence();
            _[slot].key = key;
            ret = 0;
            break;
        } else {
            LOCK = INVALID;
        }
    }
    lock = sema;
    while (!CAS(&sema, &lock, lock-1)) {
        lock = sema;
    }
    return ret;
#endif
}

template <typename K, typename V>
void Segment<K, V>::Insert4split(K& key, V value, size_t loc) {
    for (unsigned i = 0; i < kNumPairPerCacheLine * kNumCacheLine; ++i) {
        auto slot = (loc+i) % kNumSlot;
        if (_[slot].key == INVALID) {
            _[slot].key = key;
            _[slot].value = value;
            return;
        }
    }
}

template <typename K, typename V>
Segment<K, V>** Segment<K, V>::Split(void) {
    using namespace std;
    int64_t lock = 0;
    if (!CAS(&sema, &lock, -1)) return nullptr;

#ifdef INPLACE
    Segment** split = new Segment*[2];
  split[0] = this;
  split[1] = new Segment(local_depth+1);

  for (unsigned i = 0; i < kNumSlot; ++i) {
    auto key_hash = h(&_[i].key, sizeof(K));
    if (key_hash & ((size_t) 1 << ((sizeof(K)*8 - local_depth - 1)))) {
      split[1]->Insert4split
        (_[i].key, _[i].value, (key_hash & kMask)*kNumPairPerCacheLine);
    }
  }

  clflush((char*)split[1], sizeof(Segment));
  local_depth = local_depth + 1;
  clflush((char*)&local_depth, sizeof(size_t));

  return split;
#else
    Segment** split = new Segment*[2];
    split[0] = new Segment(local_depth+1);
    split[1] = new Segment(local_depth+1);

    for (unsigned i = 0; i < kNumSlot; ++i) {
        auto key_hash = h(&_[i].key, sizeof(K));
        if (key_hash & ((size_t) 1 << ((sizeof(K)*8 - local_depth - 1)))) {
            split[1]->Insert4split
                (_[i].key, _[i].value, (key_hash & kMask)*kNumPairPerCacheLine);
        } else {
            split[0]->Insert4split
                (_[i].key, _[i].value, (key_hash & kMask)*kNumPairPerCacheLine);
        }
    }

    clflush((char*)split[0], sizeof(Segment));
    clflush((char*)split[1], sizeof(Segment));

    return split;
#endif
}

template <typename K, typename V>
CCEH<K, V>::CCEH(void)
    : dir{new Directory<K, V>(0)}
{
    for (unsigned i = 0; i < dir->capacity; ++i) {
        dir->_[i] = new Segment<K, V>(0);
        dir->_[i]->pattern = i;
    }
}

template <typename K, typename V>
CCEH<K, V>::CCEH(size_t initCap)
    : dir{new Directory<K, V>(static_cast<size_t>(log2(initCap)))}
{
    for (unsigned i = 0; i < dir->capacity; ++i) {
        dir->_[i] = new Segment<K, V>(static_cast<size_t>(log2(initCap)));
        dir->_[i]->pattern = i;
    }
}

template <typename K, typename V>
CCEH<K, V>::~CCEH(void)
{ }

template <typename K, typename V>
void Directory<K, V>::LSBUpdate(int local_depth, int global_depth, int dir_cap, int x, Segment<K, V>** s) {
    int depth_diff = global_depth - local_depth;
    if (depth_diff == 0) {
        if ((x % dir_cap) >= dir_cap/2) {
            _[x-dir_cap/2] = s[0];
            clflush((char*)&_[x-dir_cap/2], sizeof(Segment<K, V>*));
            _[x] = s[1];
            clflush((char*)&_[x], sizeof(Segment<K, V>*));
        } else {
            _[x] = s[0];
            clflush((char*)&_[x], sizeof(Segment<K, V>*));
            _[x+dir_cap/2] = s[1];
            clflush((char*)&_[x+dir_cap/2], sizeof(Segment<K, V>*));
        }
    } else {
        if ((x%dir_cap) >= dir_cap/2) {
            LSBUpdate(local_depth+1, global_depth, dir_cap/2, x-dir_cap/2, s);
            LSBUpdate(local_depth+1, global_depth, dir_cap/2, x, s);
        } else {
            LSBUpdate(local_depth+1, global_depth, dir_cap/2, x, s);
            LSBUpdate(local_depth+1, global_depth, dir_cap/2, x+dir_cap/2, s);
        }
    }
    return;
}

template <typename K, typename V>
void CCEH<K, V>::Insert(K& key, V value) {
    STARTOVER:
    auto key_hash = h(&key, sizeof(key));
    auto y = (key_hash & kMask) * kNumPairPerCacheLine;

    RETRY:
    auto x = (key_hash >> (8*sizeof(key_hash)-dir->depth));
    auto target = dir->_[x];
    auto ret = target->Insert(key, value, y, key_hash);

    if (ret == 1) {
        Segment<K, V>** s = target->Split();
        if (s == nullptr) {
            // another thread is doing split
            goto RETRY;
        }

        s[0]->pattern = (key_hash >> (8*sizeof(key_hash)-s[0]->local_depth+1)) << 1;
        s[1]->pattern = ((key_hash >> (8*sizeof(key_hash)-s[1]->local_depth+1)) << 1) + 1;

        // Directory management
        while (!dir->Acquire()) {
            asm("nop");
        }
        { // CRITICAL SECTION - directory update
            x = (key_hash >> (8*sizeof(key_hash)-dir->depth));
#ifdef INPLACE
            if (dir->_[x]->local_depth-1 < dir->depth) {  // normal split
#else
            if (dir->_[x]->local_depth < dir->depth) {  // normal split
#endif
                unsigned depth_diff = dir->depth - s[0]->local_depth;
                if (depth_diff == 0) {
                    if (x%2 == 0) {
                        dir->_[x+1] = s[1];
#ifdef INPLACE
                        clflush((char*) &dir->_[x+1], 8);
#else
                        mfence();
                        dir->_[x] = s[0];
                        clflush((char*) &dir->_[x], 16);
#endif
                    } else {
                        dir->_[x] = s[1];
#ifdef INPLACE
                        clflush((char*) &dir->_[x], 8);
#else
                        mfence();
                        dir->_[x-1] = s[0];
                        clflush((char*) &dir->_[x-1], 16);
#endif
                    }
                } else {
                    int chunk_size = pow(2, dir->depth - (s[0]->local_depth - 1));
                    x = x - (x % chunk_size);
                    for (unsigned i = 0; i < chunk_size/2; ++i) {
                        dir->_[x+chunk_size/2+i] = s[1];
                    }
                    clflush((char*)&dir->_[x+chunk_size/2], sizeof(void*)*chunk_size/2);
#ifndef INPLACE
                    for (unsigned i = 0; i < chunk_size/2; ++i) {
                        dir->_[x+i] = s[0];
                    }
                    clflush((char*)&dir->_[x], sizeof(void*)*chunk_size/2);
#endif
                }
                while (!dir->Release()) {
                    asm("nop");
                }
            } else {  // directory doubling
                auto dir_old = dir;
                auto d = dir->_;
                // auto _dir = new Segment*[dir->capacity*2];
                auto _dir = new Directory(dir->depth+1);
                for (unsigned i = 0; i < dir->capacity; ++i) {
                    if (i == x) {
                        _dir->_[2*i] = s[0];
                        _dir->_[2*i+1] = s[1];
                    } else {
                        _dir->_[2*i] = d[i];
                        _dir->_[2*i+1] = d[i];
                    }
                }
                clflush((char*)&_dir->_[0], sizeof(Segment<K, V>*)*_dir->capacity);
                clflush((char*)&_dir, sizeof(Directory<K, V>));
                dir = _dir;
                clflush((char*)&dir, sizeof(void*));
                delete dir_old;
                // TODO: requiered to do this atomically
            }
#ifdef INPLACE
            s[0]->sema = 0;
#endif
        }  // End of critical section
        goto RETRY;
    } else if (ret == 2) {
        // Insert(key, value);
        goto STARTOVER;
    } else {
        clflush((char*)&dir->_[x]->_[y], 64);
    }
}

// This function does not allow resizing
template <typename K, typename V>
bool CCEH<K, V>::InsertOnly(K& key, V value) {
    auto key_hash = h(&key, sizeof(key));
    auto x = (key_hash >> (8*sizeof(key_hash)-dir->depth));
    auto y = (key_hash & kMask) * kNumPairPerCacheLine;

    auto ret = dir->_[x]->Insert(key, value, y, key_hash);
    if (ret == 0) {
        clflush((char*)&dir->_[x]->_[y], 64);
        return true;
    }

    return false;
}

// TODO
template <typename K, typename V>
bool CCEH<K, V>::Delete(K& key) {
    return false;
}

template <typename K, typename V>
V CCEH<K, V>::Get(K& key) {
    auto key_hash = h(&key, sizeof(key));
    auto x = (key_hash >> (8*sizeof(key_hash)-dir->depth));
    auto y = (key_hash & kMask) * kNumPairPerCacheLine;

    auto dir_ = dir->_[x];

#ifdef INPLACE
    auto sema = dir->_[x]->sema;
  while (!CAS(&dir->_[x]->sema, &sema, sema+1)) {
    sema = dir->_[x]->sema;
  }
#endif

    for (unsigned i = 0; i < kNumPairPerCacheLine * kNumCacheLine; ++i) {
        auto slot = (y+i) % Segment<K, V>::kNumSlot;
        if (dir_->_[slot].key == key) {
#ifdef INPLACE
            sema = dir->_[x]->sema;
      while (!CAS(&dir->_[x]->sema, &sema, sema-1)) {
        sema = dir->_[x]->sema;
      }
#endif
            return dir_->_[slot].value;
        }
    }

#ifdef INPLACE
    sema = dir->_[x]->sema;
  while (!CAS(&dir->_[x]->sema, &sema, sema-1)) {
    sema = dir->_[x]->sema;
  }
#endif
    return NONE;
}

template <typename K, typename V>
double CCEH<K, V>::Utilization(void) {
    size_t sum = 0;
    std::unordered_map<Segment<K, V>*, bool> set;
    for (size_t i = 0; i < dir->capacity; ++i) {
        set[dir->_[i]] = true;
    }
    for (auto& elem: set) {
        for (unsigned i = 0; i < Segment<K, V>::kNumSlot; ++i) {
#ifdef INPLACE
            auto key_hash = h(&elem.first->_[i].key, sizeof(elem.first->_[i].key));
      if (key_hash >> (8*sizeof(key_hash)-elem.first->local_depth) == elem.first->pattern) sum++;
#else
            if (elem.first->_[i].key != INVALID) sum++;
#endif
        }
    }
    return ((double)sum)/((double)set.size()*Segment<K, V>::kNumSlot)*100.0;
}

template <typename K, typename V>
size_t CCEH<K, V>::Capacity(void) {
    std::unordered_map<Segment<K, V>*, bool> set;
    for (size_t i = 0; i < dir->capacity; ++i) {
        set[dir->_[i]] = true;
    }
    return set.size() * Segment<K, V>::kNumSlot;
}

template <typename K, typename V>
size_t Segment<K, V>::numElem(void) {
    size_t sum = 0;
    for (unsigned i = 0; i < kNumSlot; ++i) {
        if (_[i].key != INVALID) {
            sum++;
        }
    }
    return sum;
}

template <typename K, typename V>
bool CCEH<K, V>::Recovery(void) {
    bool recovered = false;
    size_t i = 0;
    while (i < dir->capacity) {
        size_t depth_cur = dir->_[i]->local_depth;
        size_t stride = pow(2, dir->depth - depth_cur);
        size_t buddy = i + stride;
        if (buddy == dir->capacity) break;
        for (int j = buddy - 1; i < j; j--) {
            if (dir->_[j]->local_depth != depth_cur) {
                dir->_[j] = dir->_[i];
            }
        }
        i = i+stride;
    }
    if (recovered) {
        clflush((char*)&dir->_[0], sizeof(void*)*dir->capacity);
    }
    return recovered;
}

// for debugging
template <typename K, typename V>
V CCEH<K, V>::FindAnyway(K& key) {
    using namespace std;
    for (size_t i = 0; i < dir->capacity; ++i) {
        for (size_t j = 0; j < Segment<K, V>::kNumSlot; ++j) {
            if (dir->_[i]->_[j].key == key) {
                auto key_hash = h(&key, sizeof(key));
                auto x = (key_hash >> (8*sizeof(key_hash)-dir->depth));
                auto y = (key_hash & kMask) * kNumPairPerCacheLine;
                cout << bitset<32>(i) << endl << bitset<32>((x>>1)) << endl << bitset<32>(x) << endl;
                return dir->_[i]->_[j].value;
            }
        }
    }
    return NONE;
}

template <typename K, typename V>
void Directory<K, V>::SanityCheck(void* addr) {
    using namespace std;
    for (unsigned i = 0; i < capacity; ++i) {
        if (_[i] == addr) {
            cout << i << " " << _[i]->sema << endl;
            exit(1);
        }
    }
}


#endif  // EXTENDIBLE_PTR_H_
