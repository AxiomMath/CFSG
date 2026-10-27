module

public import CFSG.LieType.Chevalley.SignCharacterCertificates

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def e7SignReps : List (List Bool) :=
  [[false, false, false, false, false, false, false], [true, false, false, false, false, false,
    false], [false, true, false, false, false, false, false], [true, true, false, false, false,
    false, false]]

@[expose] def e7SignOrbit : List (List Bool × ℕ × List ℕ) :=
  [([false, false, false, false, false, false, false], 0, []), ([true, false, false, false, false,
    false, false], 1, []), ([true, false, true, false, false, false, false], 1, [0]), ([false,
    false, true, true, false, false, false], 1, [2, 0]), ([false, true, false, true, true, false,
    false], 1, [3, 2, 0]), ([false, true, false, false, true, false, false], 1, [1, 3, 2, 0]),
    ([false, true, false, false, true, true, false], 1, [4, 3, 2, 0]), ([false, true, false, true,
    true, true, false], 1, [4, 1, 3, 2, 0]), ([false, true, false, false, false, true, true], 1, [5,
    4, 3, 2, 0]), ([false, false, true, true, false, true, false], 1, [3, 4, 1, 3, 2, 0]), ([false,
    true, false, true, false, true, true], 1, [5, 4, 1, 3, 2, 0]), ([false, true, false, false,
    false, false, true], 1, [6, 5, 4, 3, 2, 0]), ([true, false, true, false, false, true, false], 1,
    [2, 3, 4, 1, 3, 2, 0]), ([false, false, true, true, true, true, true], 1, [5, 3, 4, 1, 3, 2,
    0]), ([false, true, false, true, false, false, true], 1, [6, 5, 4, 1, 3, 2, 0]), ([true, false,
    false, false, false, true, false], 1, [0, 2, 3, 4, 1, 3, 2, 0]), ([true, false, true, false,
    true, true, true], 1, [5, 2, 3, 4, 1, 3, 2, 0]), ([false, false, true, false, true, false,
    true], 1, [4, 5, 3, 4, 1, 3, 2, 0]), ([false, false, true, true, true, false, true], 1, [6, 5,
    3, 4, 1, 3, 2, 0]), ([true, false, false, false, true, true, true], 1, [5, 0, 2, 3, 4, 1, 3, 2,
    0]), ([true, false, true, true, true, false, true], 1, [4, 5, 2, 3, 4, 1, 3, 2, 0]), ([true,
    false, true, false, true, false, true], 1, [6, 5, 2, 3, 4, 1, 3, 2, 0]), ([false, false, true,
    false, true, true, true], 1, [6, 4, 5, 3, 4, 1, 3, 2, 0]), ([true, false, false, true, true,
    false, true], 1, [4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, false, false, false, true, false,
    true], 1, [6, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, true, false, true, false, false, true], 1,
    [3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), ([true, false, true, true, true, true, true], 1, [6, 4, 5, 2,
    3, 4, 1, 3, 2, 0]), ([false, false, true, false, false, true, false], 1, [5, 6, 4, 5, 3, 4, 1,
    3, 2, 0]), ([true, true, true, true, false, false, true], 1, [3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, false, true, true, true, true], 1, [6, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true,
    true, false, false, false, false, true], 1, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), ([true, true,
    false, true, false, true, true], 1, [6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), ([true, false, true,
    true, false, true, false], 1, [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0]), ([true, true, true, false,
    false, false, true], 1, [1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([false, true, true, false,
    false, false, true], 1, [2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, true, true, true, false,
    true, true], 1, [6, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, false, false, true, false, true,
    false], 1, [5, 6, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, true, false, false, false, true,
    true], 1, [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), ([true, true, false, true, true, true, false],
    1, [5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), ([false, true, true, true, false, false, true], 1, [2,
    1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, true, true, false, false, true, true], 1, [6, 1,
    3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([false, true, true, false, false, true, true], 1, [6, 2, 3,
    4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, true, true, true, true, true, false], 1, [5, 6, 3, 4, 5,
    0, 2, 3, 4, 1, 3, 2, 0]), ([true, true, false, false, true, true, false], 1, [5, 6, 1, 3, 4, 5,
    2, 3, 4, 1, 3, 2, 0]), ([true, true, false, false, true, false, false], 1, [4, 5, 6, 3, 4, 5, 2,
    3, 4, 1, 3, 2, 0]), ([false, false, false, true, true, false, true], 1, [3, 2, 1, 3, 4, 5, 0, 2,
    3, 4, 1, 3, 2, 0]), ([false, true, true, true, false, true, true], 1, [6, 2, 1, 3, 4, 5, 0, 2,
    3, 4, 1, 3, 2, 0]), ([true, true, true, false, true, true, false], 1, [5, 6, 1, 3, 4, 5, 0, 2,
    3, 4, 1, 3, 2, 0]), ([false, true, true, false, true, true, false], 1, [5, 6, 2, 3, 4, 5, 0, 2,
    3, 4, 1, 3, 2, 0]), ([true, true, true, false, true, false, false], 1, [4, 5, 6, 3, 4, 5, 0, 2,
    3, 4, 1, 3, 2, 0]), ([true, true, false, true, true, false, false], 1, [4, 5, 6, 1, 3, 4, 5, 2,
    3, 4, 1, 3, 2, 0]), ([false, false, false, false, true, true, true], 1, [4, 3, 2, 1, 3, 4, 5, 0,
    2, 3, 4, 1, 3, 2, 0]), ([false, false, false, true, true, true, true], 1, [6, 3, 2, 1, 3, 4, 5,
    0, 2, 3, 4, 1, 3, 2, 0]), ([false, true, true, true, true, true, false], 1, [5, 6, 2, 1, 3, 4,
    5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, true, true, true, true, false, false], 1, [4, 5, 6, 1, 3,
    4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([false, true, true, true, true, false, false], 1, [4, 5, 6, 2,
    3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, false, true, true, false, false, false], 1, [3, 4, 5,
    6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), ([false, false, false, false, false, true, false], 1, [5,
    4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([false, false, false, false, true, false, true],
    1, [6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([false, false, false, true, false, true,
    false], 1, [5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([false, true, true, false, true,
    false, false], 1, [4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([true, false, false, true,
    false, false, false], 1, [3, 4, 5, 6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]), ([false, false,
    false, true, false, false, false], 1, [3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, true, false, false, false, false], 1, [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3,
    2, 0]), ([false, true, false, false, false, false, false], 2, []), ([false, true, false, true,
    false, false, false], 2, [1]), ([false, false, true, true, true, false, false], 2, [3, 1]),
    ([true, false, true, false, true, false, false], 2, [2, 3, 1]), ([false, false, true, false,
    true, true, false], 2, [4, 3, 1]), ([true, false, false, false, true, false, false], 2, [0, 2,
    3, 1]), ([true, false, true, true, true, true, false], 2, [4, 2, 3, 1]), ([false, false, true,
    false, false, true, true], 2, [5, 4, 3, 1]), ([true, false, false, true, true, true, false], 2,
    [4, 0, 2, 3, 1]), ([true, true, false, true, false, true, false], 2, [3, 4, 2, 3, 1]), ([true,
    false, true, true, false, true, true], 2, [5, 4, 2, 3, 1]), ([false, false, true, false, false,
    false, true], 2, [6, 5, 4, 3, 1]), ([true, true, true, true, false, true, false], 2, [3, 4, 0,
    2, 3, 1]), ([true, false, false, true, false, true, true], 2, [5, 4, 0, 2, 3, 1]), ([true, true,
    false, false, false, true, false], 2, [1, 3, 4, 2, 3, 1]), ([true, true, false, true, true,
    true, true], 2, [5, 3, 4, 2, 3, 1]), ([true, false, true, true, false, false, true], 2, [6, 5,
    4, 2, 3, 1]), ([true, true, true, false, false, true, false], 2, [1, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, false, false, true, false], 2, [2, 3, 4, 0, 2, 3, 1]), ([true, true, true,
    true, true, true, true], 2, [5, 3, 4, 0, 2, 3, 1]), ([true, false, false, true, false, false,
    true], 2, [6, 5, 4, 0, 2, 3, 1]), ([true, true, false, false, true, true, true], 2, [5, 1, 3, 4,
    2, 3, 1]), ([true, true, false, false, true, false, true], 2, [4, 5, 3, 4, 2, 3, 1]), ([true,
    true, false, true, true, false, true], 2, [6, 5, 3, 4, 2, 3, 1]), ([false, true, true, true,
    false, true, false], 2, [2, 1, 3, 4, 0, 2, 3, 1]), ([true, true, true, false, true, true, true],
    2, [5, 1, 3, 4, 0, 2, 3, 1]), ([false, true, true, false, true, true, true], 2, [5, 2, 3, 4, 0,
    2, 3, 1]), ([true, true, true, false, true, false, true], 2, [4, 5, 3, 4, 0, 2, 3, 1]), ([true,
    true, true, true, true, false, true], 2, [6, 5, 3, 4, 0, 2, 3, 1]), ([false, false, false, true,
    true, true, false], 2, [3, 2, 1, 3, 4, 0, 2, 3, 1]), ([false, true, true, true, true, true,
    true], 2, [5, 2, 1, 3, 4, 0, 2, 3, 1]), ([false, true, true, true, true, false, true], 2, [4, 5,
    2, 3, 4, 0, 2, 3, 1]), ([false, true, true, false, true, false, true], 2, [6, 5, 2, 3, 4, 0, 2,
    3, 1]), ([false, false, false, false, true, false, false], 2, [4, 3, 2, 1, 3, 4, 0, 2, 3, 1]),
    ([false, false, false, true, false, true, true], 2, [5, 3, 2, 1, 3, 4, 0, 2, 3, 1]), ([false,
    false, false, true, false, false, true], 2, [3, 4, 5, 2, 3, 4, 0, 2, 3, 1]), ([true, true,
    false, false, false, false, false], 3, []), ([true, true, true, false, false, false, false], 3,
    [0]), ([true, true, false, true, false, false, false], 3, [1]), ([true, true, true, true, false,
    false, false], 3, [1, 0]), ([false, true, true, true, false, false, false], 3, [2, 0]), ([true,
    false, true, true, true, false, false], 3, [3, 1]), ([false, true, true, false, false, false,
    false], 3, [2, 1, 0]), ([true, false, false, true, true, false, false], 3, [3, 1, 0]), ([false,
    false, false, true, true, false, false], 3, [3, 2, 0]), ([false, false, true, false, true,
    false, false], 3, [2, 3, 1]), ([true, false, true, false, true, true, false], 3, [4, 3, 1]),
    ([true, false, false, false, true, true, false], 3, [4, 3, 1, 0]), ([false, false, false, false,
    true, true, false], 3, [4, 3, 2, 0]), ([false, false, true, true, true, true, false], 3, [4, 2,
    3, 1]), ([true, false, true, false, false, true, true], 3, [5, 4, 3, 1]), ([true, false, false,
    false, false, true, true], 3, [5, 4, 3, 1, 0]), ([false, false, false, false, false, true,
    true], 3, [5, 4, 3, 2, 0]), ([false, true, false, true, false, true, false], 3, [3, 4, 2, 3,
    1]), ([false, false, true, true, false, true, true], 3, [5, 4, 2, 3, 1]), ([true, false, true,
    false, false, false, true], 3, [6, 5, 4, 3, 1]), ([true, false, false, false, false, false,
    true], 3, [6, 5, 4, 3, 1, 0]), ([false, false, false, false, false, false, true], 3, [6, 5, 4,
    3, 2, 0]), ([false, true, false, false, false, true, false], 3, [1, 3, 4, 2, 3, 1]), ([false,
    true, false, true, true, true, true], 3, [5, 3, 4, 2, 3, 1]), ([false, false, true, true, false,
    false, true], 3, [6, 5, 4, 2, 3, 1]), ([false, true, false, false, true, true, true], 3, [5, 1,
    3, 4, 2, 3, 1]), ([false, true, false, false, true, false, true], 3, [4, 5, 3, 4, 2, 3, 1]),
    ([false, true, false, true, true, false, true], 3, [6, 5, 3, 4, 2, 3, 1])]

@[expose] def e7SignStab0
    : StabCert where
  mask := [false, false, false, false, false, false, false]
  simple := [0, 1, 2, 3, 4, 5, 6]
  elems :=
    [[0, 1, 2, 3, 4, 5, 6]]

@[expose] def e7SignStab1
    : StabCert where
  mask := [true, false, false, false, false, false, false]
  simple := [1, 2, 3, 4, 5, 6, 124]
  elems :=
    [[0, 1, 2, 3, 4, 5, 6], [7, 1, 8, 3, 4, 5, 6], [20, 1, 0, 12, 4, 5, 6], [32, 10, 0, 2, 14, 5,
      6], [44, 3, 0, 2, 24, 5, 6], [45, 24, 0, 2, 3, 16, 6], [56, 14, 0, 2, 10, 16, 6], [57, 38, 0,
      2, 3, 4, 18], [67, 4, 0, 12, 1, 28, 6], [68, 28, 0, 2, 10, 4, 18], [69, 52, 0, 2, 3, 4, 5],
      [77, 4, 8, 3, 1, 40, 6], [78, 16, 0, 12, 1, 14, 18], [79, 42, 0, 2, 10, 4, 5], [77, 4, 2, 3,
      1, 47, 6], [86, 16, 8, 3, 1, 26, 18], [87, 5, 0, 26, 1, 3, 30], [88, 30, 0, 12, 1, 14, 5],
      [86, 16, 2, 3, 1, 34, 18], [94, 5, 8, 14, 1, 12, 30], [95, 30, 8, 3, 1, 26, 5], [96, 18, 0,
      26, 1, 3, 16], [94, 5, 2, 14, 1, 21, 30], [95, 30, 2, 3, 1, 34, 5], [101, 5, 21, 4, 10, 2,
      42], [102, 18, 8, 14, 1, 12, 16], [103, 6, 0, 40, 1, 3, 4], [101, 5, 12, 4, 10, 8, 42], [102,
      18, 2, 14, 1, 21, 16], [107, 5, 33, 4, 3, 2, 52], [108, 18, 21, 4, 10, 2, 28], [109, 6, 8, 28,
      1, 12, 4], [107, 5, 23, 4, 3, 8, 52], [101, 5, 3, 4, 23, 0, 54], [108, 18, 12, 4, 10, 8, 28],
      [109, 6, 2, 28, 1, 21, 4], [112, 18, 33, 4, 3, 2, 38], [113, 6, 21, 16, 10, 2, 14], [107, 5,
      10, 4, 12, 0, 65], [112, 18, 23, 4, 3, 8, 38], [108, 18, 3, 4, 23, 0, 40], [113, 6, 12, 16,
      10, 8, 14], [116, 6, 33, 16, 3, 2, 24], [117, 6, 34, 5, 24, 2, 3], [107, 5, 1, 14, 2, 0, 76],
      [112, 18, 10, 4, 12, 0, 51], [116, 6, 23, 16, 3, 8, 24], [113, 6, 3, 16, 23, 0, 26], [117, 6,
      26, 5, 24, 8, 3], [119, 6, 46, 5, 14, 2, 10], [107, 16, 1, 3, 2, 0, 85], [112, 18, 1, 14, 2,
      0, 64], [116, 6, 10, 16, 12, 0, 37], [119, 6, 37, 5, 14, 8, 10], [117, 6, 14, 5, 37, 0, 12],
      [121, 6, 58, 5, 4, 12, 1], [107, 4, 1, 3, 2, 0, 93], [112, 30, 1, 3, 2, 0, 75], [116, 6, 1,
      28, 2, 0, 50], [119, 6, 24, 5, 26, 0, 23], [121, 6, 50, 5, 4, 21, 1], [117, 6, 4, 5, 50, 0,
      2], [123, 6, 70, 5, 4, 3, 1]]

@[expose] def e7SignStab2
    : StabCert where
  mask := [false, true, false, false, false, false, false]
  simple := [0, 2, 3, 4, 5, 6, 104]
  elems :=
    [[0, 1, 2, 3, 4, 5, 6], [0, 9, 2, 10, 4, 5, 6], [0, 22, 12, 1, 14, 5, 6], [8, 35, 3, 1, 26, 5,
      6], [0, 36, 26, 1, 3, 16, 6], [2, 44, 3, 1, 34, 5, 6], [8, 48, 14, 1, 12, 16, 6], [0, 49, 40,
      1, 3, 4, 18], [2, 56, 14, 1, 21, 16, 6], [21, 61, 4, 10, 2, 28, 6], [8, 62, 28, 1, 12, 4, 18],
      [0, 63, 54, 1, 3, 4, 5], [12, 67, 4, 10, 8, 28, 6], [2, 68, 28, 1, 21, 4, 18], [33, 61, 4, 3,
      2, 38, 6], [21, 73, 16, 10, 2, 14, 18], [8, 74, 42, 1, 12, 4, 5], [23, 67, 4, 3, 8, 38, 6],
      [3, 77, 4, 23, 0, 40, 6], [12, 78, 16, 10, 8, 14, 18], [2, 79, 42, 1, 21, 4, 5], [33, 73, 16,
      3, 2, 24, 18], [34, 83, 5, 24, 2, 3, 30], [21, 84, 30, 10, 2, 14, 5], [10, 77, 4, 12, 0, 51,
      6], [23, 78, 16, 3, 8, 24, 18], [3, 86, 16, 23, 0, 26, 18], [26, 87, 5, 24, 8, 3, 30], [12,
      88, 30, 10, 8, 14, 5], [46, 83, 5, 14, 2, 10, 30], [33, 84, 30, 3, 2, 24, 5], [34, 92, 18, 24,
      2, 3, 16], [1, 77, 14, 2, 0, 64, 6], [10, 86, 16, 12, 0, 37, 18], [37, 87, 5, 14, 8, 10, 30],
      [23, 88, 30, 3, 8, 24, 5], [14, 94, 5, 37, 0, 12, 30], [3, 95, 30, 23, 0, 26, 5], [26, 96, 18,
      24, 8, 3, 16], [58, 83, 5, 4, 12, 1, 42], [46, 92, 18, 14, 2, 10, 16], [47, 100, 6, 38, 2, 3,
      4], [1, 77, 3, 2, 0, 75, 6], [1, 86, 28, 2, 0, 50, 18], [24, 94, 5, 26, 0, 23, 30], [10, 95,
      30, 12, 0, 37, 5], [50, 87, 5, 4, 21, 1, 42], [37, 96, 18, 14, 8, 10, 16], [4, 101, 5, 50, 0,
      2, 42], [14, 102, 18, 37, 0, 12, 16], [40, 103, 6, 38, 8, 3, 4], [70, 83, 5, 4, 3, 1, 54],
      [58, 92, 18, 4, 12, 1, 28], [59, 100, 6, 28, 2, 10, 4], [1, 95, 42, 2, 0, 50, 5], [24, 102,
      18, 26, 0, 23, 16], [50, 96, 18, 4, 21, 1, 28], [51, 103, 6, 28, 8, 10, 4], [4, 108, 18, 50,
      0, 2, 28], [28, 109, 6, 51, 0, 12, 4], [70, 92, 18, 4, 3, 1, 40], [71, 100, 6, 16, 12, 1, 14],
      [38, 109, 6, 40, 0, 23, 4], [64, 103, 6, 16, 21, 1, 14], [16, 113, 6, 64, 0, 2, 14], [80, 100,
      6, 16, 3, 1, 26], [81, 100, 6, 5, 26, 1, 3], [75, 103, 6, 5, 34, 1, 3], [5, 117, 6, 75, 0, 2,
      3], [89, 100, 6, 5, 14, 1, 12], [97, 100, 6, 5, 4, 10, 2], [104, 100, 6, 5, 4, 3, 2]]

@[expose] def e7SignStab3
    : StabCert where
  mask := [true, true, false, false, false, false, false]
  simple := [2, 3, 4, 5, 6, 33]
  elems :=
    [[0, 1, 2, 3, 4, 5, 6], [7, 1, 8, 3, 4, 5, 6], [0, 9, 2, 10, 4, 5, 6], [7, 9, 8, 10, 4, 5, 6],
      [20, 1, 0, 12, 4, 5, 6], [0, 22, 12, 1, 14, 5, 6], [20, 9, 0, 23, 4, 5, 6], [7, 22, 21, 1, 14,
      5, 6], [32, 10, 0, 2, 14, 5, 6], [8, 35, 3, 1, 26, 5, 6], [0, 36, 26, 1, 3, 16, 6], [7, 36,
      34, 1, 3, 16, 6], [45, 24, 0, 2, 3, 16, 6], [8, 48, 14, 1, 12, 16, 6], [0, 49, 40, 1, 3, 4,
      18], [7, 49, 47, 1, 3, 4, 18], [57, 38, 0, 2, 3, 4, 18], [21, 61, 4, 10, 2, 28, 6], [8, 62,
      28, 1, 12, 4, 18], [0, 63, 54, 1, 3, 4, 5], [7, 63, 60, 1, 3, 4, 5], [69, 52, 0, 2, 3, 4, 5],
      [33, 61, 4, 3, 2, 38, 6], [21, 73, 16, 10, 2, 14, 18], [8, 74, 42, 1, 12, 4, 5], [33, 73, 16,
      3, 2, 24, 18], [34, 83, 5, 24, 2, 3, 30], [21, 84, 30, 10, 2, 14, 5], [46, 83, 5, 14, 2, 10,
      30], [33, 84, 30, 3, 2, 24, 5], [34, 92, 18, 24, 2, 3, 16], [58, 83, 5, 4, 12, 1, 42], [46,
      92, 18, 14, 2, 10, 16], [47, 100, 6, 38, 2, 3, 4], [70, 83, 5, 4, 3, 1, 54], [58, 92, 18, 4,
      12, 1, 28], [59, 100, 6, 28, 2, 10, 4], [70, 87, 5, 4, 3, 1, 60], [70, 92, 18, 4, 3, 1, 40],
      [71, 100, 6, 16, 12, 1, 14], [70, 96, 18, 4, 3, 1, 47], [80, 100, 6, 16, 3, 1, 26], [81, 100,
      6, 5, 26, 1, 3], [80, 103, 6, 16, 3, 1, 34], [89, 100, 6, 5, 14, 1, 12], [89, 103, 6, 5, 14,
      1, 21], [97, 100, 6, 5, 4, 10, 2], [97, 103, 6, 5, 4, 10, 8], [104, 100, 6, 5, 4, 3, 2], [104,
      103, 6, 5, 4, 3, 8], [97, 109, 6, 5, 4, 23, 0], [104, 109, 6, 5, 4, 12, 0], [104, 113, 6, 5,
      14, 2, 0], [104, 117, 6, 16, 3, 2, 0], [104, 117, 18, 4, 3, 2, 0], [110, 117, 5, 4, 3, 2, 0]]

theorem e7SignOrbit_check : OrbitCheck .E7 e7SignReps e7SignOrbit := by
  unfold OrbitCheck
  decide +kernel

theorem e7SignStab0_check
    : e7SignStab0.check e7Certificate = true := by
  decide +kernel

theorem e7SignStab0_passing
    : (e7SignStab0.passing e7Certificate).length ≤ 2 := by
  decide +kernel

theorem e7SignStab1_check
    : e7SignStab1.check e7Certificate = true := by
  decide +kernel

theorem e7SignStab1_passing
    : (e7SignStab1.passing e7Certificate).length ≤ 2 := by
  decide +kernel

theorem e7SignStab2_check
    : e7SignStab2.check e7Certificate = true := by
  decide +kernel

theorem e7SignStab2_passing
    : (e7SignStab2.passing e7Certificate).length ≤ 2 := by
  decide +kernel

theorem e7SignStab3_check
    : e7SignStab3.check e7Certificate = true := by
  decide +kernel

theorem e7SignStab3_passing
    : (e7SignStab3.passing e7Certificate).length ≤ 2 := by
  decide +kernel

theorem card_kernelPosStabilizer_le_E7
    : ∀ ρ < e7SignReps.length,
    Nat.card (kernelPosStabilizer (maskChar (τ := .E7) (listMask (e7SignReps.getD ρ [])))) ≤ 2 := by
  intro ρ hρ
  have hlen : e7SignReps.length = 4 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact (StabCert.card_kernelPosStabilizer_le e7Certificate_check e7SignStab0_check).trans
      e7SignStab0_passing
  · exact (StabCert.card_kernelPosStabilizer_le e7Certificate_check e7SignStab1_check).trans
      e7SignStab1_passing
  · exact (StabCert.card_kernelPosStabilizer_le e7Certificate_check e7SignStab2_check).trans
      e7SignStab2_passing
  · exact (StabCert.card_kernelPosStabilizer_le e7Certificate_check e7SignStab3_check).trans
      e7SignStab3_passing

end CFSG.LieType.Chevalley
