cmake_minimum_required(VERSION 3.10)
project(icpc_management_system)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_BUILD_TYPE Release)

add_executable(code code.cpp)

# Optimize aggressively for speed
target_compile_options(code PRIVATE -O3 -DNDEBUG -flto -s)
