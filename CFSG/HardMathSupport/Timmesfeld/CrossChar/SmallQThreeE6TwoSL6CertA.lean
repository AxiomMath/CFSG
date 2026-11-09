module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoSL6Split

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open scoped MatrixGroups
open CFSG.Open

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

set_option maxRecDepth 100000 in
theorem dCert_z001_0 : dCert [wordMask (zword ![0, 0, 1]),
    wordMask (zword ![0, 1, 0])]
    [[1, 18, 4, 32, 2, 40]] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z001_1 : dCert [wordMask (zword ![0, 0, 1]),
    wordMask (zword ![1, 0, 0])]
    [[4, 18, 5, 8, 2, 32]] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z001_2 : dCert [wordMask (zword ![0, 0, 1]),
    wordMask (zword ![0, 1, 0] ++ zword ![1, 0, 0])]
    [[9, 18, 36, 1, 2, 4],
      [37, 18, 41, 1, 2, 4],
      [44, 18, 13, 1, 2, 4],
      [12, 18, 37, 1, 2, 4],
      [13, 18, 33, 1, 2, 4]] = true := by
  exact dCert_of_pl (L35 := [(0, 0)] ++ [(1, 4)] ++ [(4, 5)] ++ [(5, 1)] ++ [(8, 32)] ++ [(9, 36)] ++ [(12, 37)] ++ [(13, 33)] ++ [(32, 40)] ++ [(33, 44)] ++ [(36, 45)] ++ [(37, 41)] ++ [(40, 8)] ++ [(41, 12)] ++ [(44, 13)] ++ [(45, 9)])
    (L02 := [(0, 0), (1, 4), (4, 5), (5, 1), (8, 32), (9, 36), (12, 37), (13, 33), (32, 40), (33, 44), (36, 45), (37, 41), (40, 8), (41, 12), (44, 13), (45, 9)])
    (L41 := [(0, 0), (2, 18), (16, 2), (18, 16)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

set_option maxRecDepth 100000 in
theorem dCert_z001_3 : dCert [wordMask (zword ![0, 0, 1]),
    wordMask (zword ![0, 1, 0] ++ zword ![1, 0, 0] ++
      zword ![1, 0, 0])]
    [[9, 18, 44, 1, 2, 5],
      [36, 18, 13, 1, 2, 5],
      [45, 18, 33, 1, 2, 5],
      [12, 18, 45, 1, 2, 5],
      [13, 18, 41, 1, 2, 5]] = true := by
  exact dCert_of_pl (L35 := [(0, 0)] ++ [(1, 5)] ++ [(4, 1)] ++ [(5, 4)] ++ [(8, 32)] ++ [(9, 37)] ++ [(12, 33)] ++ [(13, 36)] ++ [(32, 40)] ++ [(33, 45)] ++ [(36, 41)] ++ [(37, 44)] ++ [(40, 8)] ++ [(41, 13)] ++ [(44, 9)] ++ [(45, 12)])
    (L02 := [(0, 0), (1, 4), (4, 5), (5, 1), (8, 40), (9, 44), (12, 45), (13, 41), (32, 8), (33, 12), (36, 13), (37, 9), (40, 32), (41, 36), (44, 37), (45, 33)])
    (L41 := [(0, 0), (2, 18), (16, 2), (18, 16)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

theorem zFacts_z001 : zFacts ![0, 0, 1] ![0, 1, 0] ![1, 0, 0] = true := by
  decide +kernel

theorem gLAPPrimeCoreOf_centralizer_zSL_z001 (hK : Nat.card K = 2) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({zSL ![0, 0, 1]} : Set SL(6, K))) = ⊥ :=
  gLAPPrimeCoreOf_centralizer_zSL_eq_bot hK _ _ _ zFacts_z001 dCert_z001_0 dCert_z001_1
    dCert_z001_2 dCert_z001_3

set_option maxRecDepth 100000 in
theorem dCert_z110_0 : dCert [wordMask (zword ![1, 1, 0]),
    wordMask (zword ![0, 0, 1])]
    [[9, 18, 36, 1, 2, 4],
      [37, 18, 41, 1, 2, 4],
      [44, 18, 13, 1, 2, 4],
      [12, 18, 37, 1, 2, 4],
      [13, 18, 33, 1, 2, 4]] = true := by
  exact dCert_of_pl (L35 := [(0, 0)] ++ [(1, 4)] ++ [(4, 5)] ++ [(5, 1)] ++ [(8, 32)] ++ [(9, 36)] ++ [(12, 37)] ++ [(13, 33)] ++ [(32, 40)] ++ [(33, 44)] ++ [(36, 45)] ++ [(37, 41)] ++ [(40, 8)] ++ [(41, 12)] ++ [(44, 13)] ++ [(45, 9)])
    (L02 := [(0, 0), (1, 4), (4, 5), (5, 1), (8, 32), (9, 36), (12, 37), (13, 33), (32, 40), (33, 44), (36, 45), (37, 41), (40, 8), (41, 12), (44, 13), (45, 9)])
    (L41 := [(0, 0), (2, 18), (16, 2), (18, 16)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

set_option maxRecDepth 100000 in
theorem dCert_z110_1 : dCert [wordMask (zword ![1, 1, 0]),
    wordMask (zword ![0, 1, 0])]
    [[1, 18, 4, 8, 2, 32]] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z110_2 : dCert [wordMask (zword ![1, 1, 0]),
    wordMask (zword ![0, 0, 1] ++ zword ![0, 1, 0])]
    [] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z110_3 : dCert [wordMask (zword ![1, 1, 0]),
    wordMask (zword ![0, 0, 1] ++ zword ![0, 1, 0] ++
      zword ![0, 1, 0])]
    [] = true := by
  decide +kernel

theorem zFacts_z110 : zFacts ![1, 1, 0] ![0, 0, 1] ![0, 1, 0] = true := by
  decide +kernel

theorem gLAPPrimeCoreOf_centralizer_zSL_z110 (hK : Nat.card K = 2) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({zSL ![1, 1, 0]} : Set SL(6, K))) = ⊥ :=
  gLAPPrimeCoreOf_centralizer_zSL_eq_bot hK _ _ _ zFacts_z110 dCert_z110_0 dCert_z110_1
    dCert_z110_2 dCert_z110_3

set_option maxRecDepth 100000 in
theorem dCert_z011_0 : dCert [wordMask (zword ![0, 1, 1]),
    wordMask (zword ![0, 0, 1])]
    [[1, 18, 4, 32, 2, 40]] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z011_1 : dCert [wordMask (zword ![0, 1, 1]),
    wordMask (zword ![1, 0, 0])]
    [[1, 18, 4, 8, 2, 32],
      [1, 22, 4, 8, 3, 32],
      [1, 23, 4, 8, 6, 32],
      [1, 19, 4, 8, 7, 32],
      [2, 4, 18, 8, 1, 32],
      [2, 5, 18, 8, 4, 32],
      [2, 1, 18, 8, 5, 32]] = true := by
  exact dCert_of_pl (L35 := [(0, 0)] ++ [(8, 32)] ++ [(32, 40)] ++ [(40, 8)])
    (L02 := [(0, 0), (1, 4), (2, 18), (3, 22)] ++ [(4, 5), (5, 1), (6, 23), (7, 19)] ++ [(16, 2), (17, 6), (18, 16), (19, 20)] ++ [(20, 7), (21, 3), (22, 21), (23, 17)])
    (L41 := [(0, 0), (1, 4), (2, 18), (3, 22), (4, 5), (5, 1), (6, 23), (7, 19), (16, 2), (17, 6), (18, 16), (19, 20), (20, 7), (21, 3), (22, 21), (23, 17)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (all_append_of (all_append_of (all_append_of (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))) (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))) (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)))

set_option maxRecDepth 100000 in
theorem dCert_z011_2 : dCert [wordMask (zword ![0, 1, 1]),
    wordMask (zword ![0, 0, 1] ++ zword ![1, 0, 0])]
    [] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z011_3 : dCert [wordMask (zword ![0, 1, 1]),
    wordMask (zword ![0, 0, 1] ++ zword ![1, 0, 0] ++
      zword ![1, 0, 0])]
    [] = true := by
  decide +kernel

theorem zFacts_z011 : zFacts ![0, 1, 1] ![0, 0, 1] ![1, 0, 0] = true := by
  decide +kernel

theorem gLAPPrimeCoreOf_centralizer_zSL_z011 (hK : Nat.card K = 2) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({zSL ![0, 1, 1]} : Set SL(6, K))) = ⊥ :=
  gLAPPrimeCoreOf_centralizer_zSL_eq_bot hK _ _ _ zFacts_z011 dCert_z011_0 dCert_z011_1
    dCert_z011_2 dCert_z011_3

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
