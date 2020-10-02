add_library(
        CCEH

        cceh/CCEH_MSB.cpp
        cceh/CCEH.h
        cceh/uhash.h
        cceh/pair.h
        cceh/persist.h
)

set_target_properties(CCEH PROPERTIES LINKER_LANGUAGE CXX)
