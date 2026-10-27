module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoSL6

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
  decide +kernel

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
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z121_1 : dCert [wordMask (zword ![1, 2, 1]),
    wordMask (zword ![0, 1, 0])]
    [[1, 50, 4, 2, 10, 18],
      [1, 48, 4, 10, 26, 50],
      [1, 34, 4, 2, 24, 18],
      [1, 40, 4, 2, 32, 18],
      [1, 8, 4, 2, 40, 18]] = true := by
  decide +kernel

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
  decide +kernel

theorem zFacts_z121 : zFacts ![1, 2, 1] ![0, 0, 1] ![0, 1, 0] = true := by
  decide +kernel

theorem gLAPPrimeCoreOf_centralizer_zSL_z121 (hK : Nat.card K = 2) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({zSL ![1, 2, 1]} : Set SL(6, K))) = ⊥ :=
  gLAPPrimeCoreOf_centralizer_zSL_eq_bot hK _ _ _ zFacts_z121 dCert_z121_0 dCert_z121_1
    dCert_z121_2 dCert_z121_3

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
