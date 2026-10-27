module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodCheck

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration

theorem e8Two_classCheck :
    classCheck Tag.E8.rank (cartanList Tag.E8) e8TwoMat Tag.E8.artifactRoots 2 [] = true := by
  decide +kernel

theorem e8Four_classCheck :
    classCheck Tag.E8.rank (cartanList Tag.E8) e8FourMat Tag.E8.artifactRoots 4 [] = true := by
  decide +kernel

@[expose] def e8EightCert : List (ℕ × ℕ × ℕ) :=
  [(136, 4, 6), (142, 4, 7), (147, 4, 8), (155, 4, 13), (164, 4, 14), (174, 4, 17), (177, 4, 20), (184, 4, 22), (197, 4, 33), (207, 4, 43), (214, 4, 52), (224, 4, 70), (229, 4, 87), (234, 4, 109), (0, 4, 110), (3, 4, 113), (236, 4, 126), (239, 4, 129), (5, 4, 130), (10, 4, 152), (15, 4, 169), (25, 4, 187), (32, 4, 196), (42, 4, 206), (55, 4, 217), (62, 4, 219), (65, 4, 222), (75, 4, 225), (84, 4, 226), (92, 4, 231), (97, 4, 232), (103, 4, 233), (144, 6, 11), (146, 6, 13), (162, 6, 14), (172, 6, 24), (178, 6, 30), (205, 6, 57), (212, 6, 64), (2, 6, 101), (237, 6, 138), (27, 6, 175), (34, 6, 182), (61, 6, 209), (67, 6, 215), (77, 6, 225), (93, 6, 226), (95, 6, 228), (66, 6, 214), (135, 6, 234), (104, 6, 5), (173, 6, 25), (139, 7, 12), (165, 7, 17), (167, 7, 19), (192, 7, 44), (198, 7, 50), (201, 7, 53), (1, 7, 94), (238, 7, 145), (38, 7, 186), (41, 7, 189), (47, 7, 195), (72, 7, 220), (74, 7, 222), (100, 7, 227), (49, 7, 197), (190, 7, 42), (132, 8, 11), (183, 8, 45), (56, 8, 194), (107, 8, 228), (108, 8, 229), (131, 8, 10), (40, 8, 178), (90, 8, 2), (149, 8, 237), (199, 8, 61), (127, 9, 11), (128, 9, 12), (111, 9, 227), (112, 9, 228), (51, 9, 183), (188, 9, 56), (123, 11, 229), (116, 11, 10), (120, 12, 13), (204, 12, 71), (35, 12, 168), (119, 12, 226), (78, 12, 0), (82, 12, 3), (157, 12, 236), (161, 12, 239), (81, 13, 3), (158, 13, 236)]

theorem e8Eight_classCheck :
    classCheck Tag.E8.rank (cartanList Tag.E8) e8EightMat Tag.E8.artifactRoots 8 e8EightCert = true := by
  decide +kernel

theorem e7Two_classCheck :
    classCheck Tag.E7.rank (cartanList Tag.E7) e7TwoMat Tag.E7.artifactRoots 2 [] = true := by
  decide +kernel

@[expose] def e7ThreeCert : List (ℕ × ℕ × ℕ) :=
  [(93, 0, 1), (94, 0, 2), (95, 0, 3), (96, 0, 4), (97, 0, 5), (99, 0, 7), (100, 0, 8), (101, 0, 9), (103, 0, 11), (104, 0, 12), (106, 0, 14), (109, 0, 17), (110, 0, 18), (112, 0, 20), (115, 0, 23), (119, 0, 27), (6, 0, 98), (10, 0, 102), (13, 0, 105), (15, 0, 107), (16, 0, 108), (19, 0, 111), (21, 0, 113), (22, 0, 114), (24, 0, 116), (25, 0, 117), (26, 0, 118), (28, 0, 120), (29, 0, 121), (30, 0, 122), (31, 0, 123), (32, 0, 124), (73, 1, 2), (74, 1, 3), (75, 1, 4), (76, 1, 5), (83, 1, 7), (84, 1, 8), (85, 1, 9), (87, 1, 11), (88, 1, 12), (90, 1, 14), (35, 1, 111), (37, 1, 113), (38, 1, 114), (40, 1, 116), (41, 1, 117), (42, 1, 118), (49, 1, 120), (50, 1, 121), (51, 1, 122), (52, 1, 123), (69, 2, 3), (70, 2, 4), (71, 2, 5), (79, 2, 7), (80, 2, 8), (81, 2, 9), (44, 2, 116), (45, 2, 117), (46, 2, 118), (54, 2, 120), (55, 2, 121), (56, 2, 122), (66, 3, 4), (67, 3, 5), (78, 3, 7), (47, 3, 118), (58, 3, 120), (59, 3, 121), (64, 4, 5), (61, 4, 120)]

theorem e7Three_classCheck :
    classCheck Tag.E7.rank (cartanList Tag.E7) e7ThreeMat Tag.E7.artifactRoots 3 e7ThreeCert = true := by
  decide +kernel

@[expose] def e7SixCert : List (ℕ × ℕ × ℕ) :=
  [(66, 3, 4), (80, 3, 11), (84, 3, 17), (90, 3, 23), (91, 3, 24), (0, 3, 30), (100, 3, 33), (106, 3, 39), (107, 3, 40), (112, 3, 43), (113, 3, 44), (118, 3, 47), (1, 3, 51), (2, 3, 56), (119, 3, 57), (120, 3, 58), (5, 3, 67), (6, 3, 68), (123, 3, 69), (124, 3, 74), (7, 3, 78), (12, 3, 81), (13, 3, 82), (18, 3, 85), (19, 3, 86), (25, 3, 92), (125, 3, 95), (34, 3, 101), (35, 3, 102), (41, 3, 108), (45, 3, 114), (59, 3, 121), (79, 4, 11), (83, 4, 17), (88, 4, 23), (89, 4, 24), (99, 4, 33), (104, 4, 39), (105, 4, 40), (110, 4, 43), (111, 4, 44), (117, 4, 47), (8, 4, 78), (14, 4, 81), (15, 4, 82), (20, 4, 85), (21, 4, 86), (26, 4, 92), (36, 4, 101), (37, 4, 102), (42, 4, 108), (46, 4, 114), (63, 9, 10), (72, 9, 16), (77, 9, 22), (98, 9, 38), (27, 9, 87), (48, 9, 103), (53, 9, 109), (62, 9, 115), (71, 10, 16), (76, 10, 22), (97, 10, 38), (28, 10, 87), (49, 10, 103), (54, 10, 109), (73, 11, 17), (94, 11, 33), (31, 11, 92), (52, 11, 108), (93, 17, 33), (32, 17, 92)]

theorem e7Six_classCheck :
    classCheck Tag.E7.rank (cartanList Tag.E7) e7SixMat Tag.E7.artifactRoots 6 e7SixCert = true := by
  decide +kernel

theorem twE6One_classCheck :
    classCheck Tag.E6.rank (cartanList Tag.E6) twE6OneMat Tag.E6.artifactRoots 1 [] = true := by
  decide +kernel

theorem twE6Two_classCheck :
    classCheck Tag.E6.rank (cartanList Tag.E6) twE6TwoMat Tag.E6.artifactRoots 2 [] = true := by
  decide +kernel

@[expose] def triD4OneMat : List (List ℤ) := [[0, 0, 0, 1], [1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0]]

theorem triD4One_classCheck :
    classCheck Tag.D4.rank (cartanList Tag.D4) triD4OneMat Tag.D4.artifactRoots 1 [] = true := by
  decide +kernel

@[expose] def triD4TwoMat : List (List ℤ) := [[-1, 1, 0, 0], [0, 1, 0, -1], [0, 2, -1, 0], [0, 1, 0, 0]]

theorem triD4Two_classCheck :
    classCheck Tag.D4.rank (cartanList Tag.D4) triD4TwoMat Tag.D4.artifactRoots 2 [] = true := by
  decide +kernel

end CFSG.HardMathSupport.Timmesfeld.LangTorus
