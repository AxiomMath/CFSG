module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoSL6Split

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open scoped MatrixGroups
open CFSG.Open

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

set_option maxRecDepth 100000 in
theorem dCert_z012_0 : dCert [wordMask (zword ![0, 1, 2]),
    wordMask (zword ![0, 0, 1])]
    [[1, 18, 4, 32, 2, 40]] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z012_1 : dCert [wordMask (zword ![0, 1, 2]),
    wordMask (zword ![1, 0, 0])]
    [[1, 18, 4, 8, 2, 32],
      [1, 23, 4, 8, 3, 32],
      [1, 19, 4, 8, 6, 32],
      [1, 22, 4, 8, 7, 32],
      [2, 5, 16, 8, 1, 32],
      [2, 1, 16, 8, 4, 32],
      [2, 4, 16, 8, 5, 32]] = true := by
  exact dCert_of_pl (L35 := [(0, 0)] ++ [(8, 32)] ++ [(32, 40)] ++ [(40, 8)])
    (L02 := [(0, 0), (1, 4), (2, 16), (3, 20)] ++ [(4, 5), (5, 1), (6, 21), (7, 17)] ++ [(16, 18), (17, 22), (18, 2), (19, 6)] ++ [(20, 23), (21, 19), (22, 7), (23, 3)])
    (L41 := [(0, 0), (1, 5), (2, 18), (3, 23), (4, 1), (5, 4), (6, 19), (7, 22), (16, 2), (17, 7), (18, 16), (19, 21), (20, 3), (21, 6), (22, 17), (23, 20)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (all_append_of (all_append_of (all_append_of (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))) (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))) (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)))

set_option maxRecDepth 100000 in
theorem dCert_z012_2 : dCert [wordMask (zword ![0, 1, 2]),
    wordMask (zword ![0, 0, 1] ++ zword ![1, 0, 0])]
    [] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z012_3 : dCert [wordMask (zword ![0, 1, 2]),
    wordMask (zword ![0, 0, 1] ++ zword ![1, 0, 0] ++
      zword ![1, 0, 0])]
    [] = true := by
  decide +kernel

theorem zFacts_z012 : zFacts ![0, 1, 2] ![0, 0, 1] ![1, 0, 0] = true := by
  decide +kernel

theorem gLAPPrimeCoreOf_centralizer_zSL_z012 (hK : Nat.card K = 2) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({zSL ![0, 1, 2]} : Set SL(6, K))) = ⊥ :=
  gLAPPrimeCoreOf_centralizer_zSL_eq_bot hK _ _ _ zFacts_z012 dCert_z012_0 dCert_z012_1
    dCert_z012_2 dCert_z012_3

set_option maxRecDepth 100000 in
theorem dCert_z121_0 : dCert [wordMask (zword ![1, 2, 1]),
    wordMask (zword ![0, 0, 1])]
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

set_option maxRecDepth 100000 in
theorem dCert_z121_1 : dCert [wordMask (zword ![1, 2, 1]),
    wordMask (zword ![0, 1, 0])]
    [[1, 50, 4, 2, 10, 18],
      [1, 48, 4, 10, 26, 50],
      [1, 34, 4, 2, 24, 18],
      [1, 40, 4, 2, 32, 18],
      [1, 8, 4, 2, 40, 18]] = true := by
  exact dCert_of_pl (L35 := [(0, 0)] ++ [(2, 18)] ++ [(8, 32)] ++ [(10, 50)] ++ [(16, 2)] ++ [(18, 16)] ++ [(24, 34)] ++ [(26, 48)] ++ [(32, 40)] ++ [(34, 58)] ++ [(40, 8)] ++ [(42, 26)] ++ [(48, 42)] ++ [(50, 56)] ++ [(56, 10)] ++ [(58, 24)])
    (L02 := [(0, 0), (1, 4), (4, 5), (5, 1)])
    (L41 := [(0, 0), (2, 18), (8, 32), (10, 50), (16, 2), (18, 16), (24, 34), (26, 48), (32, 40), (34, 58), (40, 8), (42, 26), (48, 42), (50, 56), (56, 10), (58, 24)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (all_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

set_option maxRecDepth 100000 in
theorem dCert_z121_2 : dCert [wordMask (zword ![1, 2, 1]),
    wordMask (zword ![0, 0, 1] ++ zword ![0, 1, 0])]
    [] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z121_3 : dCert [wordMask (zword ![1, 2, 1]),
    wordMask (zword ![0, 0, 1] ++ zword ![0, 1, 0] ++
      zword ![0, 1, 0])]
    [[1, 18, 4, 8, 2, 32],
      [1, 23, 4, 8, 3, 32],
      [1, 19, 4, 8, 6, 32],
      [1, 22, 4, 8, 7, 32],
      [2, 5, 16, 8, 1, 32],
      [2, 1, 16, 8, 4, 32],
      [2, 4, 16, 8, 5, 32]] = true := by
  exact dCert_of_pl (L35 := [(0, 0)] ++ [(8, 32)] ++ [(32, 40)] ++ [(40, 8)])
    (L02 := [(0, 0), (1, 4), (2, 16), (3, 20)] ++ [(4, 5), (5, 1), (6, 21), (7, 17)] ++ [(16, 18), (17, 22), (18, 2), (19, 6)] ++ [(20, 23), (21, 19), (22, 7), (23, 3)])
    (L41 := [(0, 0), (1, 5), (2, 18), (3, 23), (4, 1), (5, 4), (6, 19), (7, 22), (16, 2), (17, 7), (18, 16), (19, 21), (20, 3), (21, 6), (22, 17), (23, 20)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (all_append_of (all_append_of (all_append_of (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))) (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))) (all_single_append_of (all_single_append_of (all_single_append_of (by decide +kernel) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)))

theorem zFacts_z121 : zFacts ![1, 2, 1] ![0, 0, 1] ![0, 1, 0] = true := by
  decide +kernel

theorem gLAPPrimeCoreOf_centralizer_zSL_z121 (hK : Nat.card K = 2) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({zSL ![1, 2, 1]} : Set SL(6, K))) = ⊥ :=
  gLAPPrimeCoreOf_centralizer_zSL_eq_bot hK _ _ _ zFacts_z121 dCert_z121_0 dCert_z121_1
    dCert_z121_2 dCert_z121_3

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
