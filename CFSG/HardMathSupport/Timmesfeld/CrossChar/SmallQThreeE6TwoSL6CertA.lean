module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoSL6

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
  decide +kernel

set_option maxRecDepth 100000 in
theorem dCert_z001_3 : dCert [wordMask (zword ![0, 0, 1]),
    wordMask (zword ![0, 1, 0] ++ zword ![1, 0, 0] ++
      zword ![1, 0, 0])]
    [[9, 18, 44, 1, 2, 5],
      [36, 18, 13, 1, 2, 5],
      [45, 18, 33, 1, 2, 5],
      [12, 18, 45, 1, 2, 5],
      [13, 18, 41, 1, 2, 5]] = true := by
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
