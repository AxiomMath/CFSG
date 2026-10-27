module

public import Certificates.Data.CFSGNative.Fi22.Data

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.F3.Native CFSG.Sporadic.Fi22.Native

set_option compiler.extract_closed false

@[expose] def fi22HeisProg : List (List Nat) := [
    [1, 2], [1, 3], [2, 1], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [5, 6], [7, 3], [8, 8], [9, 9],
    [1, 9], [11, 10], [3, 2], [13, 2], [14, 2], [15, 2], [16, 2], [17, 2], [18, 2], [16, 19],
    [20, 20], [21, 12], [22, 20], [4, 4, 4, 4, 4, 4, 4], [17, 3], [13, 19], [24, 25], [27, 26],
    [28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28], [23, 29, 29, 29, 28, 12, 12], [30, 30, 30, 30],
    [23, 28, 28, 29, 28, 23, 28, 23, 29], [32, 32, 32, 32], [28, 12, 12, 12, 23, 23, 12, 23, 28],
    [34, 34, 34, 34], [12, 29, 29, 23, 12], [36, 36, 36, 36], [28, 12, 23, 12, 28, 23, 12],
    [38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38, 38], [12, 29, 12, 28, 28],
    [40, 40, 40, 40], [23, 23, 29, 12, 12, 23, 23, 12, 23, 29, 23], [42, 42, 42, 42], [31, 43],
    [39, 39], [33, 33, 37]]

@[expose] def fi22HeisX1 : Nat := 31

@[expose] def fi22HeisX2 : Nat := 35

@[expose] def fi22HeisX3 : Nat := 44

@[expose] def fi22HeisY1 : Nat := 33

@[expose] def fi22HeisY2 : Nat := 45

@[expose] def fi22HeisY3 : Nat := 46

@[expose] def fi22HeisZ : Nat := 41

@[expose] def fi22HeisRels : List (List Nat × List Nat) :=
  [
   ([fi22HeisX1, fi22HeisX1, fi22HeisX1], []), ([fi22HeisX2, fi22HeisX2, fi22HeisX2], []),
   ([fi22HeisX3, fi22HeisX3, fi22HeisX3], []),
   ([fi22HeisY1, fi22HeisY1, fi22HeisY1], []), ([fi22HeisY2, fi22HeisY2, fi22HeisY2], []),
   ([fi22HeisY3, fi22HeisY3, fi22HeisY3], []),
   ([fi22HeisZ, fi22HeisZ, fi22HeisZ], []),
   ([fi22HeisX1, fi22HeisZ], [fi22HeisZ, fi22HeisX1]),
   ([fi22HeisX2, fi22HeisZ], [fi22HeisZ, fi22HeisX2]),
   ([fi22HeisX3, fi22HeisZ], [fi22HeisZ, fi22HeisX3]),
   ([fi22HeisY1, fi22HeisZ], [fi22HeisZ, fi22HeisY1]),
   ([fi22HeisY2, fi22HeisZ], [fi22HeisZ, fi22HeisY2]),
   ([fi22HeisY3, fi22HeisZ], [fi22HeisZ, fi22HeisY3]),
   ([fi22HeisX1, fi22HeisY1], [fi22HeisY1, fi22HeisX1, fi22HeisZ]),
   ([fi22HeisX2, fi22HeisY2], [fi22HeisY2, fi22HeisX2, fi22HeisZ]),
   ([fi22HeisX3, fi22HeisY3], [fi22HeisY3, fi22HeisX3, fi22HeisZ]),
   ([fi22HeisX1, fi22HeisX2], [fi22HeisX2, fi22HeisX1]),
   ([fi22HeisX1, fi22HeisX3], [fi22HeisX3, fi22HeisX1]),
   ([fi22HeisX2, fi22HeisX3], [fi22HeisX3, fi22HeisX2]),
   ([fi22HeisY1, fi22HeisY2], [fi22HeisY2, fi22HeisY1]),
   ([fi22HeisY1, fi22HeisY3], [fi22HeisY3, fi22HeisY1]),
   ([fi22HeisY2, fi22HeisY3], [fi22HeisY3, fi22HeisY2]),
   ([fi22HeisX1, fi22HeisY2], [fi22HeisY2, fi22HeisX1]),
   ([fi22HeisX1, fi22HeisY3], [fi22HeisY3, fi22HeisX1]),
   ([fi22HeisX2, fi22HeisY1], [fi22HeisY1, fi22HeisX2]),
   ([fi22HeisX2, fi22HeisY3], [fi22HeisY3, fi22HeisX2]),
   ([fi22HeisX3, fi22HeisY1], [fi22HeisY1, fi22HeisX3]),
   ([fi22HeisX3, fi22HeisY2], [fi22HeisY2, fi22HeisX3])]

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
