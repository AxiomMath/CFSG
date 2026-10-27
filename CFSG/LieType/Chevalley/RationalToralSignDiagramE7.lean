module

public import CFSG.LieType.Chevalley.RationalToralSignDiagramOrbits
public import CFSG.LieType.Chevalley.RationalToralSignDiagramCheck

public section

namespace CFSG.LieType.Chevalley.ToralSign

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def e7Orbit0 : OrbitEntries :=
  [([false, false, false, false, false, false, false], [])]

@[expose] def e7Orbit1 : OrbitEntries :=
  [([true, false, false, false, false, false, false], []),
    ([true, false, true, false, false, false, false], [0]),
    ([false, false, true, true, false, false, false], [2, 0]),
    ([false, true, false, true, true, false, false], [3, 2, 0]),
    ([false, true, false, false, true, false, false], [1, 3, 2, 0]),
    ([false, true, false, false, true, true, false], [4, 3, 2, 0]),
    ([false, true, false, true, true, true, false], [4, 1, 3, 2, 0]),
    ([false, true, false, false, false, true, true], [5, 4, 3, 2, 0]),
    ([false, false, true, true, false, true, false], [3, 4, 1, 3, 2, 0]),
    ([false, true, false, true, false, true, true], [5, 4, 1, 3, 2, 0]),
    ([false, true, false, false, false, false, true], [6, 5, 4, 3, 2, 0]),
    ([true, false, true, false, false, true, false], [2, 3, 4, 1, 3, 2, 0]),
    ([false, false, true, true, true, true, true], [5, 3, 4, 1, 3, 2, 0]),
    ([false, true, false, true, false, false, true], [6, 5, 4, 1, 3, 2, 0]),
    ([true, false, false, false, false, true, false], [0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, true, false, true, true, true], [5, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, true, false, true, false, true], [4, 5, 3, 4, 1, 3, 2, 0]),
    ([false, false, true, true, true, false, true], [6, 5, 3, 4, 1, 3, 2, 0]),
    ([true, false, false, false, true, true, true], [5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, true, true, true, false, true], [4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, true, false, true, false, true], [6, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, true, false, true, true, true], [6, 4, 5, 3, 4, 1, 3, 2, 0]),
    ([true, false, false, true, true, false, true], [4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, false, false, true, false, true], [6, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, false, true, false, false, true], [3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, true, true, true, true, true], [6, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, true, false, false, true, false], [5, 6, 4, 5, 3, 4, 1, 3, 2, 0]),
    ([true, true, true, true, false, false, true], [3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, false, true, true, true, true], [6, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, false, false, false, false, true], [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, false, true, false, true, true], [6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, true, true, false, true, false], [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, true, false, false, false, true], [1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, true, true, false, false, false, true], [2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, true, true, false, true, true], [6, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, false, true, false, true, false], [5, 6, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, false, false, false, true, true], [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, false, true, true, true, false], [5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([false, true, true, true, false, false, true], [2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, true, false, false, true, true], [6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, true, true, false, false, true, true], [6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, true, true, true, true, false], [5, 6, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, false, false, true, true, false], [5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, false, false, true, false, false], [4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, false, true, true, false, true], [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, true, true, true, false, true, true], [6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, true, false, true, true, false], [5, 6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, true, true, false, true, true, false], [5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, true, false, true, false, false], [4, 5, 6, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, false, true, true, false, false], [4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, false, false, true, true, true],
      [4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, false, true, true, true, true], [6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, true, true, true, true, true, false], [5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, true, true, true, true, false, false], [4, 5, 6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, true, true, true, true, false, false], [4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, true, true, false, false, false],
      [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, false, false, false, true, false],
      [5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, false, false, true, false, true],
      [6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, false, true, false, true, false],
      [5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, true, true, false, true, false, false],
      [4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([true, false, false, true, false, false, false],
      [3, 4, 5, 6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, false, true, false, false, false],
      [3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]),
    ([false, false, true, false, false, false, false],
      [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0])]

@[expose] def e7Orbit2 : OrbitEntries :=
  [([false, true, false, false, false, false, false], []),
    ([false, true, false, true, false, false, false], [1]),
    ([false, false, true, true, true, false, false], [3, 1]),
    ([true, false, true, false, true, false, false], [2, 3, 1]),
    ([false, false, true, false, true, true, false], [4, 3, 1]),
    ([true, false, false, false, true, false, false], [0, 2, 3, 1]),
    ([true, false, true, true, true, true, false], [4, 2, 3, 1]),
    ([false, false, true, false, false, true, true], [5, 4, 3, 1]),
    ([true, false, false, true, true, true, false], [4, 0, 2, 3, 1]),
    ([true, true, false, true, false, true, false], [3, 4, 2, 3, 1]),
    ([true, false, true, true, false, true, true], [5, 4, 2, 3, 1]),
    ([false, false, true, false, false, false, true], [6, 5, 4, 3, 1]),
    ([true, true, true, true, false, true, false], [3, 4, 0, 2, 3, 1]),
    ([true, false, false, true, false, true, true], [5, 4, 0, 2, 3, 1]),
    ([true, true, false, false, false, true, false], [1, 3, 4, 2, 3, 1]),
    ([true, true, false, true, true, true, true], [5, 3, 4, 2, 3, 1]),
    ([true, false, true, true, false, false, true], [6, 5, 4, 2, 3, 1]),
    ([true, true, true, false, false, true, false], [1, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, false, false, true, false], [2, 3, 4, 0, 2, 3, 1]),
    ([true, true, true, true, true, true, true], [5, 3, 4, 0, 2, 3, 1]),
    ([true, false, false, true, false, false, true], [6, 5, 4, 0, 2, 3, 1]),
    ([true, true, false, false, true, true, true], [5, 1, 3, 4, 2, 3, 1]),
    ([true, true, false, false, true, false, true], [4, 5, 3, 4, 2, 3, 1]),
    ([true, true, false, true, true, false, true], [6, 5, 3, 4, 2, 3, 1]),
    ([false, true, true, true, false, true, false], [2, 1, 3, 4, 0, 2, 3, 1]),
    ([true, true, true, false, true, true, true], [5, 1, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, false, true, true, true], [5, 2, 3, 4, 0, 2, 3, 1]),
    ([true, true, true, false, true, false, true], [4, 5, 3, 4, 0, 2, 3, 1]),
    ([true, true, true, true, true, false, true], [6, 5, 3, 4, 0, 2, 3, 1]),
    ([false, false, false, true, true, true, false], [3, 2, 1, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, true, true, true, true], [5, 2, 1, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, true, true, false, true], [4, 5, 2, 3, 4, 0, 2, 3, 1]),
    ([false, true, true, false, true, false, true], [6, 5, 2, 3, 4, 0, 2, 3, 1]),
    ([false, false, false, false, true, false, false], [4, 3, 2, 1, 3, 4, 0, 2, 3, 1]),
    ([false, false, false, true, false, true, true], [5, 3, 2, 1, 3, 4, 0, 2, 3, 1]),
    ([false, false, false, true, false, false, true], [3, 4, 5, 2, 3, 4, 0, 2, 3, 1])]

@[expose] def e7Orbit3 : OrbitEntries :=
  [([true, true, false, false, false, false, false], []),
    ([true, true, true, false, false, false, false], [0]),
    ([true, true, false, true, false, false, false], [1]),
    ([true, true, true, true, false, false, false], [1, 0]),
    ([false, true, true, true, false, false, false], [2, 0]),
    ([true, false, true, true, true, false, false], [3, 1]),
    ([false, true, true, false, false, false, false], [2, 1, 0]),
    ([true, false, false, true, true, false, false], [3, 1, 0]),
    ([false, false, false, true, true, false, false], [3, 2, 0]),
    ([false, false, true, false, true, false, false], [2, 3, 1]),
    ([true, false, true, false, true, true, false], [4, 3, 1]),
    ([true, false, false, false, true, true, false], [4, 3, 1, 0]),
    ([false, false, false, false, true, true, false], [4, 3, 2, 0]),
    ([false, false, true, true, true, true, false], [4, 2, 3, 1]),
    ([true, false, true, false, false, true, true], [5, 4, 3, 1]),
    ([true, false, false, false, false, true, true], [5, 4, 3, 1, 0]),
    ([false, false, false, false, false, true, true], [5, 4, 3, 2, 0]),
    ([false, true, false, true, false, true, false], [3, 4, 2, 3, 1]),
    ([false, false, true, true, false, true, true], [5, 4, 2, 3, 1]),
    ([true, false, true, false, false, false, true], [6, 5, 4, 3, 1]),
    ([true, false, false, false, false, false, true], [6, 5, 4, 3, 1, 0]),
    ([false, false, false, false, false, false, true], [6, 5, 4, 3, 2, 0]),
    ([false, true, false, false, false, true, false], [1, 3, 4, 2, 3, 1]),
    ([false, true, false, true, true, true, true], [5, 3, 4, 2, 3, 1]),
    ([false, false, true, true, false, false, true], [6, 5, 4, 2, 3, 1]),
    ([false, true, false, false, true, true, true], [5, 1, 3, 4, 2, 3, 1]),
    ([false, true, false, false, true, false, true], [4, 5, 3, 4, 2, 3, 1]),
    ([false, true, false, true, true, false, true], [6, 5, 3, 4, 2, 3, 1])]

@[expose] def e7RhoIdx : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
    74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
    98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
    117, 118, 119, 120, 121, 122, 123, 124, 125]

@[expose] def e7Splus0 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 21, 23, 24, 26, 28, 30, 33, 34, 37, 38, 40, 42, 46,
    47, 50, 51, 52, 54, 58, 59, 60, 64, 65, 70, 71, 72, 75, 76, 80, 81, 82, 85, 89, 90, 91, 93, 97,
    98, 99, 104, 105, 106, 110, 111, 114, 115, 118, 120, 122, 124]

@[expose] def e7Delta0 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6]

@[expose] def e7Paths0_0 : List (ℕ × List ℕ) :=
  [(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (6, []), (7, [0]), (8, [2]), (9, [1]),
    (10, [3]), (11, [2]), (12, [3]), (13, [3]), (14, [4]), (15, [4]), (16, [5]), (17, [5]),
    (18, [6]), (19, [6]), (20, [2, 0]), (21, [3, 2]), (22, [3, 1]), (23, [2, 3]), (24, [4, 3]),
    (25, [3, 2]), (26, [4, 3]), (27, [4, 3]), (28, [5, 4]), (29, [5, 4]), (30, [6, 5]),
    (31, [6, 5]), (32, [3, 2, 0]), (33, [1, 3, 2]), (34, [4, 3, 2]), (35, [2, 3, 1]),
    (36, [4, 3, 1]), (37, [4, 2, 3]), (38, [5, 4, 3]), (39, [4, 3, 2]), (40, [5, 4, 3]),
    (41, [5, 4, 3]), (42, [6, 5, 4]), (43, [6, 5, 4]), (44, [1, 3, 2, 0]), (45, [4, 3, 2, 0]),
    (46, [4, 1, 3, 2]), (47, [5, 4, 3, 2]), (48, [4, 2, 3, 1]), (49, [5, 4, 3, 1]),
    (50, [3, 4, 2, 3]), (51, [5, 4, 2, 3]), (52, [6, 5, 4, 3]), (53, [5, 4, 3, 2]),
    (54, [6, 5, 4, 3]), (55, [6, 5, 4, 3]), (56, [4, 1, 3, 2, 0]), (57, [5, 4, 3, 2, 0]),
    (58, [3, 4, 1, 3, 2]), (59, [5, 4, 1, 3, 2]), (60, [6, 5, 4, 3, 2]), (61, [3, 4, 2, 3, 1]),
    (62, [5, 4, 2, 3, 1]), (63, [6, 5, 4, 3, 1]), (64, [5, 3, 4, 2, 3]), (65, [6, 5, 4, 2, 3]),
    (66, [6, 5, 4, 3, 2]), (67, [3, 4, 1, 3, 2, 0]), (68, [5, 4, 1, 3, 2, 0]),
    (69, [6, 5, 4, 3, 2, 0]), (70, [2, 3, 4, 1, 3, 2]), (71, [5, 3, 4, 1, 3, 2]),
    (72, [6, 5, 4, 1, 3, 2]), (73, [5, 3, 4, 2, 3, 1]), (74, [6, 5, 4, 2, 3, 1]),
    (75, [4, 5, 3, 4, 2, 3]), (76, [6, 5, 3, 4, 2, 3]), (77, [2, 3, 4, 1, 3, 2, 0]),
    (78, [5, 3, 4, 1, 3, 2, 0]), (79, [6, 5, 4, 1, 3, 2, 0]), (80, [5, 2, 3, 4, 1, 3, 2]),
    (81, [4, 5, 3, 4, 1, 3, 2]), (82, [6, 5, 3, 4, 1, 3, 2]), (83, [4, 5, 3, 4, 2, 3, 1]),
    (84, [6, 5, 3, 4, 2, 3, 1]), (85, [6, 4, 5, 3, 4, 2, 3]), (86, [5, 2, 3, 4, 1, 3, 2, 0]),
    (87, [4, 5, 3, 4, 1, 3, 2, 0]), (88, [6, 5, 3, 4, 1, 3, 2, 0]), (89, [4, 5, 2, 3, 4, 1, 3, 2]),
    (90, [6, 5, 2, 3, 4, 1, 3, 2]), (91, [6, 4, 5, 3, 4, 1, 3, 2]), (92, [6, 4, 5, 3, 4, 2, 3, 1]),
    (93, [5, 6, 4, 5, 3, 4, 2, 3]), (94, [4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (95, [6, 5, 2, 3, 4, 1, 3, 2, 0]), (96, [6, 4, 5, 3, 4, 1, 3, 2, 0]),
    (97, [3, 4, 5, 2, 3, 4, 1, 3, 2]), (98, [6, 4, 5, 2, 3, 4, 1, 3, 2]),
    (99, [5, 6, 4, 5, 3, 4, 1, 3, 2]), (100, [5, 6, 4, 5, 3, 4, 2, 3, 1]),
    (101, [3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), (102, [6, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (103, [5, 6, 4, 5, 3, 4, 1, 3, 2, 0]), (104, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (105, [6, 3, 4, 5, 2, 3, 4, 1, 3, 2]), (106, [5, 6, 4, 5, 2, 3, 4, 1, 3, 2]),
    (107, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), (108, [6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (109, [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0]), (110, [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (111, [5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2]), (112, [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (113, [5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), (114, [5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (115, [4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2]), (116, [5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (117, [4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]), (118, [4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (119, [4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (120, [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (121, [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (122, [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (123, [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0]),
    (124, [0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]),
    (125, [0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0])]

@[expose] def e7Splus1 : List ℕ :=
  [1, 2, 3, 4, 5, 6, 10, 12, 14, 16, 18, 23, 24, 26, 28, 30, 37, 38, 40, 42, 50, 51, 52, 54, 64,
    65, 75, 76, 85, 93, 124]

@[expose] def e7Delta1 : List ℕ :=
  [1, 2, 3, 4, 5, 6, 124]

@[expose] def e7Paths1_0 : List (ℕ × List ℕ) :=
  [(1, []), (2, []), (3, []), (4, []), (5, []), (6, []), (9, [1]), (10, [3]), (11, [2]),
    (12, [3]), (13, [3]), (14, [4]), (15, [4]), (16, [5]), (17, [5]), (18, [6]), (19, [6]),
    (22, [3, 1]), (23, [2, 3]), (24, [4, 3]), (25, [3, 2]), (26, [4, 3]), (27, [4, 3]),
    (28, [5, 4]), (29, [5, 4]), (30, [6, 5]), (31, [6, 5]), (35, [2, 3, 1]), (36, [4, 3, 1]),
    (37, [4, 2, 3]), (38, [5, 4, 3]), (39, [4, 3, 2]), (40, [5, 4, 3]), (41, [5, 4, 3]),
    (42, [6, 5, 4]), (43, [6, 5, 4]), (48, [4, 2, 3, 1]), (49, [5, 4, 3, 1]), (50, [3, 4, 2, 3]),
    (51, [5, 4, 2, 3]), (52, [6, 5, 4, 3]), (53, [5, 4, 3, 2]), (54, [6, 5, 4, 3]),
    (55, [6, 5, 4, 3]), (61, [3, 4, 2, 3, 1]), (62, [5, 4, 2, 3, 1]), (63, [6, 5, 4, 3, 1]),
    (64, [5, 3, 4, 2, 3]), (65, [6, 5, 4, 2, 3]), (66, [6, 5, 4, 3, 2]), (73, [5, 3, 4, 2, 3, 1]),
    (74, [6, 5, 4, 2, 3, 1]), (75, [4, 5, 3, 4, 2, 3]), (76, [6, 5, 3, 4, 2, 3]),
    (83, [4, 5, 3, 4, 2, 3, 1]), (84, [6, 5, 3, 4, 2, 3, 1]), (85, [6, 4, 5, 3, 4, 2, 3]),
    (92, [6, 4, 5, 3, 4, 2, 3, 1]), (93, [5, 6, 4, 5, 3, 4, 2, 3]),
    (100, [5, 6, 4, 5, 3, 4, 2, 3, 1]), (124, []), (125, [124])]

@[expose] def e7Splus2 : List ℕ :=
  [0, 2, 3, 4, 5, 6, 8, 12, 14, 16, 18, 21, 26, 28, 30, 34, 40, 42, 47, 54, 60, 104, 110, 114,
    118, 120, 122, 124]

@[expose] def e7Delta2 : List ℕ :=
  [0, 2, 3, 4, 5, 6, 104]

@[expose] def e7Paths2_0 : List (ℕ × List ℕ) :=
  [(0, []), (2, []), (3, []), (4, []), (5, []), (6, []), (7, [0]), (8, [2]), (11, [2]), (12, [3]),
    (13, [3]), (14, [4]), (15, [4]), (16, [5]), (17, [5]), (18, [6]), (19, [6]), (20, [2, 0]),
    (21, [3, 2]), (25, [3, 2]), (26, [4, 3]), (27, [4, 3]), (28, [5, 4]), (29, [5, 4]),
    (30, [6, 5]), (31, [6, 5]), (32, [3, 2, 0]), (34, [4, 3, 2]), (39, [4, 3, 2]), (40, [5, 4, 3]),
    (41, [5, 4, 3]), (42, [6, 5, 4]), (43, [6, 5, 4]), (45, [4, 3, 2, 0]), (47, [5, 4, 3, 2]),
    (53, [5, 4, 3, 2]), (54, [6, 5, 4, 3]), (55, [6, 5, 4, 3]), (57, [5, 4, 3, 2, 0]),
    (60, [6, 5, 4, 3, 2]), (66, [6, 5, 4, 3, 2]), (69, [6, 5, 4, 3, 2, 0]), (104, []),
    (107, [104]), (110, [104]), (112, [104, 6]), (114, [104, 6]), (116, [104, 6, 5]),
    (118, [104, 6, 5]), (119, [104, 6, 5, 4]), (120, [104, 6, 5, 4]), (121, [104, 6, 5, 4, 3]),
    (122, [104, 6, 5, 4, 3]), (123, [104, 6, 5, 4, 3, 2]), (124, [104, 6, 5, 4, 3, 2]),
    (125, [104, 6, 5, 4, 3, 2, 0])]

@[expose] def e7Paths2_1 : List (ℕ × List ℕ) :=
  [(0, []), (2, []), (3, []), (4, []), (5, []), (6, []), (7, [0]), (8, [2]), (11, [2]), (12, [3]),
    (13, [3]), (14, [4]), (15, [4]), (16, [4]), (17, [3]), (18, [2]), (19, [2]), (20, [2, 0]),
    (21, [3, 2]), (25, [3, 2]), (26, [4, 3]), (27, [4, 3]), (28, [3]), (29, [4, 3]), (30, [4, 2]),
    (31, [2, 3]), (32, [3, 2, 0]), (34, [4, 3, 2]), (39, [4, 3, 2]), (40, [3, 4, 3]), (41, [3, 4]),
    (42, [3, 4, 2]), (43, [4, 2, 3]), (45, [4, 3, 2, 0]), (47, [3, 4, 3, 2]), (53, [3, 4, 3, 2]),
    (54, [2, 3]), (55, [3, 4, 2, 3]), (57, [3, 4, 3, 2, 0]), (60, [2, 3, 4, 3, 2]),
    (66, [2, 3, 4]), (69, [2, 3, 4, 3, 2, 0]), (104, []), (107, [0]), (110, [0]), (112, [0, 2]),
    (114, [0, 2]), (116, [0, 2, 3]), (118, [4, 0, 2]), (119, [4, 0, 2, 3]), (120, [3, 4, 0, 2]),
    (121, [3, 4, 0, 2, 3]), (122, [2, 3, 4, 0, 2]), (123, [2, 3, 4, 0, 2, 3]), (124, [0, 2, 3]),
    (125, [0, 2, 3, 4])]

@[expose] def e7Splus3 : List ℕ :=
  [2, 3, 4, 5, 6, 12, 14, 16, 18, 26, 28, 30, 33, 40, 42, 46, 54, 58, 59, 70, 71, 72, 80, 81, 82,
    89, 90, 91, 97, 98, 99, 105, 106, 111, 115, 124]

@[expose] def e7Delta3 : List ℕ :=
  [2, 3, 4, 5, 6, 33]

@[expose] def e7Paths3_0 : List (ℕ × List ℕ) :=
  [(2, []), (3, []), (4, []), (5, []), (6, []), (11, [2]), (12, [3]), (13, [3]), (14, [4]),
    (15, [4]), (16, [5]), (17, [5]), (18, [6]), (19, [6]), (25, [3, 2]), (26, [4, 3]),
    (27, [4, 3]), (28, [5, 4]), (29, [5, 4]), (30, [6, 5]), (31, [6, 5]), (33, []),
    (39, [4, 3, 2]), (40, [5, 4, 3]), (41, [5, 4, 3]), (42, [6, 5, 4]), (43, [6, 5, 4]),
    (44, [33]), (46, [33]), (53, [5, 4, 3, 2]), (54, [6, 5, 4, 3]), (55, [6, 5, 4, 3]),
    (56, [33, 4]), (58, [33, 4]), (59, [33, 5]), (66, [6, 5, 4, 3, 2]), (67, [33, 4, 3]),
    (68, [33, 5, 4]), (70, [33, 4, 3]), (71, [33, 5, 4]), (72, [33, 6, 5]), (77, [33, 4, 3, 2]),
    (78, [33, 5, 4, 3]), (79, [33, 6, 5, 4]), (80, [33, 5, 4, 3]), (81, [4, 33, 5, 4]),
    (82, [33, 6, 5, 4]), (86, [33, 5, 4, 3, 2]), (87, [4, 33, 5, 4, 3]), (88, [33, 6, 5, 4, 3]),
    (89, [4, 33, 5, 4, 3]), (90, [33, 6, 5, 4, 3]), (91, [4, 33, 6, 5, 4]),
    (94, [4, 33, 5, 4, 3, 2]), (95, [33, 6, 5, 4, 3, 2]), (96, [4, 33, 6, 5, 4, 3]),
    (97, [3, 4, 33, 5, 4, 3]), (98, [4, 33, 6, 5, 4, 3]), (99, [5, 4, 33, 6, 5, 4]),
    (101, [3, 4, 33, 5, 4, 3, 2]), (102, [4, 33, 6, 5, 4, 3, 2]), (103, [5, 4, 33, 6, 5, 4, 3]),
    (105, [3, 4, 33, 6, 5, 4, 3]), (106, [5, 4, 33, 6, 5, 4, 3]), (108, [3, 4, 33, 6, 5, 4, 3, 2]),
    (109, [5, 4, 33, 6, 5, 4, 3, 2]), (111, [5, 3, 4, 33, 6, 5, 4, 3]),
    (113, [5, 3, 4, 33, 6, 5, 4, 3, 2]), (115, [4, 5, 3, 4, 33, 6, 5, 4, 3]),
    (117, [4, 5, 3, 4, 33, 6, 5, 4, 3, 2]), (124, [33, 4, 5, 3, 4, 33, 6, 5, 4, 3]),
    (125, [33, 4, 5, 3, 4, 33, 6, 5, 4, 3, 2])]

@[expose] def e7Paths3_1 : List (ℕ × List ℕ) :=
  [(2, []), (3, []), (4, []), (5, []), (6, []), (11, [2]), (12, [3]), (13, [3]), (14, [4]),
    (15, [4]), (16, [4]), (17, [3]), (18, [2]), (19, [2]), (25, [3, 2]), (26, [4, 3]),
    (27, [4, 3]), (28, [3]), (29, [4, 3]), (30, [4, 2]), (31, [2, 3]), (33, []), (39, [4, 3, 2]),
    (40, [3, 4, 3]), (41, [3, 4]), (42, [3, 4, 2]), (43, [4, 2, 3]), (44, [33]), (46, [33]),
    (53, [3, 4, 3, 2]), (54, [2, 3]), (55, [3, 4, 2, 3]), (56, [33, 4]), (58, [33, 4]),
    (59, [33, 4]), (66, [2, 3, 4]), (67, [33, 4, 3]), (68, [33, 4, 3]), (70, [33, 4, 3]),
    (71, [33, 3]), (72, [33, 4, 2]), (77, [33, 4, 3, 2]), (78, [33, 3, 4]), (79, [33, 4, 2, 3]),
    (80, [33, 3, 4, 3]), (81, [4, 33, 3]), (82, [33, 3, 4, 2]), (86, [33, 3, 4, 3, 2]),
    (87, [4, 33, 3, 4]), (88, [33, 3, 4, 2, 3]), (89, [4, 33, 3, 4, 3]), (90, [33, 2, 3]),
    (91, [4, 33, 3, 4, 2]), (94, [4, 33, 3, 4, 3, 2]), (95, [33, 2, 3, 4]),
    (96, [4, 33, 3, 4, 2, 3]), (97, [3, 4, 33, 3, 4, 3]), (98, [4, 33, 2, 3]),
    (99, [3, 4, 33, 3, 4, 2]), (101, [3, 4, 33, 3, 4, 3, 2]), (102, [4, 33, 2, 3, 4]),
    (103, [3, 4, 33, 3, 4, 2, 3]), (105, [2, 3, 4, 33, 3, 4, 3]), (106, [2, 3, 4, 33, 3, 4, 2]),
    (108, [2, 3, 4, 33, 3, 4, 3, 2]), (109, [2, 3, 4, 33, 3, 4, 2, 3]), (111, [3, 4, 33, 2, 3]),
    (113, [3, 4, 33, 2, 3, 4]), (115, [4, 3, 4, 33, 2, 3]), (117, [4, 3, 4, 33, 2, 3, 4]),
    (124, [33, 4, 3, 4, 33, 2, 3]), (125, [33, 4, 3, 4, 33, 2, 3, 4])]

@[expose] def e7OmegaWords0 : List (List (Fin Tag.E7.rank)) :=
  [[]]

@[expose] def e7OmegaWords1 : List (List (Fin Tag.E7.rank)) :=
  [[]]

@[expose] def e7Word2_1 : List (Fin Tag.E7.rank) :=
  ([1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1] : List (Fin 7))

@[expose] def e7OmegaWords2 : List (List (Fin Tag.E7.rank)) :=
  [[], e7Word2_1]

@[expose] def e7Word3_1 : List (Fin Tag.E7.rank) :=
  ([1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1] : List (Fin 7))

@[expose] def e7OmegaWords3 : List (List (Fin Tag.E7.rank)) :=
  [[], e7Word3_1]

@[expose] def e7SignDiagramReps : List (SignRep .E7) :=
  [⟨0, 1, 1, e7OmegaWords0⟩, ⟨1, 63, 1, e7OmegaWords1⟩, ⟨2, 36, 2, e7OmegaWords2⟩,
    ⟨3, 28, 2, e7OmegaWords3⟩]

@[expose] def e7OrbitCert : OrbitCert .E7 where
  stable := e7SignDiagramReps.zip [e7Orbit0, e7Orbit1, e7Orbit2, e7Orbit3]
  other := []

theorem e7OrbitCert_reps : e7OrbitCert.reps = e7SignDiagramReps :=
  rfl

theorem e7OrbitCert_check :
    e7OrbitCert.check (1 : Equiv.Perm (Fin Tag.E7.rank)) = true := by
  decide +kernel

theorem e7OrbitCert_covers : e7OrbitCert.Covers := by
  unfold OrbitCert.Covers
  decide +kernel

theorem e7_rhoCheck :
    rhoCheck e7Certificate (1 : Equiv.Perm (Fin Tag.E7.rank)) e7RhoIdx = true := by
  decide +kernel

theorem e7_splus0 : splusCheck e7Certificate 0 e7Splus0 = true := by
  decide +kernel

theorem e7_delta0 : deltaCheck e7Certificate e7Splus0 e7Delta0 = true := by
  decide +kernel

theorem e7_omega0 : e7OmegaWords0.all (omegaCheck e7Certificate 0 e7Splus0) = true := by
  decide +kernel

theorem e7_distinct0 : distinctCheck e7Certificate e7OmegaWords0 = true := by
  decide +kernel

theorem e7_card0
    : Nat.card (kernelPosStabilizer (signMaskChar .E7 0)) ≤ 1 :=
  (natCard_kernelPosStabilizer_le_of_stabCert e7Certificate_check e7SignStab0_check
    (by decide)).trans (by decide +kernel)

theorem e7_orbit0_0 :
    orbitCheck e7Certificate 0 (thetaIdx e7Certificate e7RhoIdx []) 2 = true := by
  decide +kernel

theorem e7_path0_0 : pathCheck e7Certificate 0 (thetaIdx e7Certificate e7RhoIdx []) 2
    e7Delta0 e7Paths0_0 = true := by
  decide +kernel

theorem e7_splus1 : splusCheck e7Certificate 1 e7Splus1 = true := by
  decide +kernel

theorem e7_delta1 : deltaCheck e7Certificate e7Splus1 e7Delta1 = true := by
  decide +kernel

theorem e7_omega1 : e7OmegaWords1.all (omegaCheck e7Certificate 1 e7Splus1) = true := by
  decide +kernel

theorem e7_distinct1 : distinctCheck e7Certificate e7OmegaWords1 = true := by
  decide +kernel

theorem e7_card1
    : Nat.card (kernelPosStabilizer (signMaskChar .E7 1)) ≤ 1 :=
  (natCard_kernelPosStabilizer_le_of_stabCert e7Certificate_check e7SignStab1_check
    (by decide)).trans (by decide +kernel)

theorem e7_orbit1_0 :
    orbitCheck e7Certificate 1 (thetaIdx e7Certificate e7RhoIdx []) 2 = true := by
  decide +kernel

theorem e7_path1_0 : pathCheck e7Certificate 1 (thetaIdx e7Certificate e7RhoIdx []) 2
    e7Delta1 e7Paths1_0 = true := by
  decide +kernel

theorem e7_splus2 : splusCheck e7Certificate 2 e7Splus2 = true := by
  decide +kernel

theorem e7_delta2 : deltaCheck e7Certificate e7Splus2 e7Delta2 = true := by
  decide +kernel

theorem e7_omega2 : e7OmegaWords2.all (omegaCheck e7Certificate 2 e7Splus2) = true := by
  decide +kernel

theorem e7_distinct2 : distinctCheck e7Certificate e7OmegaWords2 = true := by
  decide +kernel

theorem e7_card2
    : Nat.card (kernelPosStabilizer (signMaskChar .E7 2)) ≤ 2 :=
  (natCard_kernelPosStabilizer_le_of_stabCert e7Certificate_check e7SignStab2_check
    (by decide)).trans (by decide +kernel)

theorem e7_orbit2_0 :
    orbitCheck e7Certificate 2 (thetaIdx e7Certificate e7RhoIdx []) 2 = true := by
  decide +kernel

theorem e7_path2_0 : pathCheck e7Certificate 2 (thetaIdx e7Certificate e7RhoIdx []) 2
    e7Delta2 e7Paths2_0 = true := by
  decide +kernel

theorem e7_orbit2_1 :
    orbitCheck e7Certificate 2 (thetaIdx e7Certificate e7RhoIdx e7Word2_1) 2 = true := by
  decide +kernel

theorem e7_path2_1 : pathCheck e7Certificate 2 (thetaIdx e7Certificate e7RhoIdx e7Word2_1) 2
    e7Delta2 e7Paths2_1 = true := by
  decide +kernel

theorem e7_splus3 : splusCheck e7Certificate 3 e7Splus3 = true := by
  decide +kernel

theorem e7_delta3 : deltaCheck e7Certificate e7Splus3 e7Delta3 = true := by
  decide +kernel

theorem e7_omega3 : e7OmegaWords3.all (omegaCheck e7Certificate 3 e7Splus3) = true := by
  decide +kernel

theorem e7_distinct3 : distinctCheck e7Certificate e7OmegaWords3 = true := by
  decide +kernel

theorem e7_card3
    : Nat.card (kernelPosStabilizer (signMaskChar .E7 3)) ≤ 2 :=
  (natCard_kernelPosStabilizer_le_of_stabCert e7Certificate_check e7SignStab3_check
    (by decide)).trans (by decide +kernel)

theorem e7_orbit3_0 :
    orbitCheck e7Certificate 3 (thetaIdx e7Certificate e7RhoIdx []) 2 = true := by
  decide +kernel

theorem e7_path3_0 : pathCheck e7Certificate 3 (thetaIdx e7Certificate e7RhoIdx []) 2
    e7Delta3 e7Paths3_0 = true := by
  decide +kernel

theorem e7_orbit3_1 :
    orbitCheck e7Certificate 3 (thetaIdx e7Certificate e7RhoIdx e7Word3_1) 2 = true := by
  decide +kernel

theorem e7_path3_1 : pathCheck e7Certificate 3 (thetaIdx e7Certificate e7RhoIdx e7Word3_1) 2
    e7Delta3 e7Paths3_1 = true := by
  decide +kernel

theorem rationalToralSignDiagram_E7 :
    RationalToralSignDiagram .E7 (1 : Equiv.Perm (Fin Tag.E7.rank)) 2
      e7SignDiagramReps := by
  rw [← e7OrbitCert_reps]
  refine RationalToralSignDiagram.of_cert e7OrbitCert_check e7OrbitCert_covers fun e he => ?_
  have hχ := OrbitCert.permChar_eq e7OrbitCert_check e he
  rw [e7OrbitCert_reps] at he
  simp only [e7SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · refine repClaims_of_check e7Certificate_check (fun _ _ => rfl) (Matrix.one_mul _)
      (by decide) hχ e7_rhoCheck e7_splus0 e7_delta0 e7_omega0 e7_distinct0
      rfl e7_card0 ?_
    · intro l hl
      simp only [e7OmegaWords0, List.mem_cons, List.mem_nil_iff, or_false] at hl
      subst hl
      exact ⟨_, e7_orbit0_0, e7_path0_0⟩
  · refine repClaims_of_check e7Certificate_check (fun _ _ => rfl) (Matrix.one_mul _)
      (by decide) hχ e7_rhoCheck e7_splus1 e7_delta1 e7_omega1 e7_distinct1
      rfl e7_card1 ?_
    · intro l hl
      simp only [e7OmegaWords1, List.mem_cons, List.mem_nil_iff, or_false] at hl
      subst hl
      exact ⟨_, e7_orbit1_0, e7_path1_0⟩
  · refine repClaims_of_check e7Certificate_check (fun _ _ => rfl) (Matrix.one_mul _)
      (by decide) hχ e7_rhoCheck e7_splus2 e7_delta2 e7_omega2 e7_distinct2
      rfl e7_card2 ?_
    · intro l hl
      simp only [e7OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · exact ⟨_, e7_orbit2_0, e7_path2_0⟩
      · exact ⟨_, e7_orbit2_1, e7_path2_1⟩
  · refine repClaims_of_check e7Certificate_check (fun _ _ => rfl) (Matrix.one_mul _)
      (by decide) hχ e7_rhoCheck e7_splus3 e7_delta3 e7_omega3 e7_distinct3
      rfl e7_card3 ?_
    · intro l hl
      simp only [e7OmegaWords3, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · exact ⟨_, e7_orbit3_0, e7_path3_0⟩
      · exact ⟨_, e7_orbit3_1, e7_path3_1⟩

end CFSG.LieType.Chevalley.ToralSign

