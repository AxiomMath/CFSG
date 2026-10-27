module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2Mats
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2

theorem quadRigid_rho : QuadRigid rho := by
  intro δ γ hd hs hδ hγ
  have a_00 := hδ 0 0
  simp [rho, Fin.sum_univ_four] at a_00
  have a_01 := hδ 0 1
  simp [rho, Fin.sum_univ_four] at a_01
  have a_02 := hδ 0 2
  simp [rho, Fin.sum_univ_four] at a_02
  have a_03 := hδ 0 3
  simp [rho, Fin.sum_univ_four] at a_03
  have a_10 := hδ 1 0
  simp [rho, Fin.sum_univ_four] at a_10
  have a_11 := hδ 1 1
  simp [rho, Fin.sum_univ_four] at a_11
  have a_12 := hδ 1 2
  simp [rho, Fin.sum_univ_four] at a_12
  have a_13 := hδ 1 3
  simp [rho, Fin.sum_univ_four] at a_13
  have b_000 := hγ 0 0 0
  simp [rho, Fin.sum_univ_four] at b_000
  have b_001 := hγ 0 0 1
  simp [rho, Fin.sum_univ_four] at b_001
  have b_002 := hγ 0 0 2
  simp [rho, Fin.sum_univ_four] at b_002
  have b_003 := hγ 0 0 3
  simp [rho, Fin.sum_univ_four] at b_003
  have b_010 := hγ 0 1 0
  simp [rho, Fin.sum_univ_four] at b_010
  have b_011 := hγ 0 1 1
  simp [rho, Fin.sum_univ_four] at b_011
  have b_012 := hγ 0 1 2
  simp [rho, Fin.sum_univ_four] at b_012
  have b_013 := hγ 0 1 3
  simp [rho, Fin.sum_univ_four] at b_013
  have b_020 := hγ 0 2 0
  simp [rho, Fin.sum_univ_four] at b_020
  have b_021 := hγ 0 2 1
  simp [rho, Fin.sum_univ_four] at b_021
  have b_022 := hγ 0 2 2
  simp [rho, Fin.sum_univ_four] at b_022
  have b_023 := hγ 0 2 3
  simp [rho, Fin.sum_univ_four] at b_023
  have b_030 := hγ 0 3 0
  simp [rho, Fin.sum_univ_four] at b_030
  have b_031 := hγ 0 3 1
  simp [rho, Fin.sum_univ_four] at b_031
  have b_032 := hγ 0 3 2
  simp [rho, Fin.sum_univ_four] at b_032
  have b_033 := hγ 0 3 3
  simp [rho, Fin.sum_univ_four] at b_033
  have b_100 := hγ 1 0 0
  simp [rho, Fin.sum_univ_four] at b_100
  have b_101 := hγ 1 0 1
  simp [rho, Fin.sum_univ_four] at b_101
  have b_102 := hγ 1 0 2
  simp [rho, Fin.sum_univ_four] at b_102
  have b_103 := hγ 1 0 3
  simp [rho, Fin.sum_univ_four] at b_103
  have b_110 := hγ 1 1 0
  simp [rho, Fin.sum_univ_four] at b_110
  have b_111 := hγ 1 1 1
  simp [rho, Fin.sum_univ_four] at b_111
  have b_112 := hγ 1 1 2
  simp [rho, Fin.sum_univ_four] at b_112
  have b_113 := hγ 1 1 3
  simp [rho, Fin.sum_univ_four] at b_113
  have b_120 := hγ 1 2 0
  simp [rho, Fin.sum_univ_four] at b_120
  have b_121 := hγ 1 2 1
  simp [rho, Fin.sum_univ_four] at b_121
  have b_122 := hγ 1 2 2
  simp [rho, Fin.sum_univ_four] at b_122
  have b_123 := hγ 1 2 3
  simp [rho, Fin.sum_univ_four] at b_123
  have b_130 := hγ 1 3 0
  simp [rho, Fin.sum_univ_four] at b_130
  have b_131 := hγ 1 3 1
  simp [rho, Fin.sum_univ_four] at b_131
  have b_132 := hγ 1 3 2
  simp [rho, Fin.sum_univ_four] at b_132
  have b_133 := hγ 1 3 3
  simp [rho, Fin.sum_univ_four] at b_133
  have d_0 := hd 0
  have d_1 := hd 1
  have d_2 := hd 2
  have d_3 := hd 3
  have s_01 := hs 0 1
  have s_02 := hs 0 2
  have s_03 := hs 0 3
  have s_12 := hs 1 2
  have s_13 := hs 1 3
  have s_23 := hs 2 3
  refine ⟨?_, ?_⟩
  · ext i; fin_cases i <;> simp <;> grind
  · ext i l; fin_cases i <;> fin_cases l <;> simp <;> grind

theorem commRigid_rho : CommRigid rho := by
  intro S h
  have c_000 := congrFun (congrFun (h 0) 0) 0
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_000
  have c_001 := congrFun (congrFun (h 0) 0) 1
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_001
  have c_002 := congrFun (congrFun (h 0) 0) 2
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_002
  have c_003 := congrFun (congrFun (h 0) 0) 3
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_003
  have c_010 := congrFun (congrFun (h 0) 1) 0
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_010
  have c_011 := congrFun (congrFun (h 0) 1) 1
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_011
  have c_012 := congrFun (congrFun (h 0) 1) 2
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_012
  have c_013 := congrFun (congrFun (h 0) 1) 3
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_013
  have c_020 := congrFun (congrFun (h 0) 2) 0
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_020
  have c_021 := congrFun (congrFun (h 0) 2) 1
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_021
  have c_022 := congrFun (congrFun (h 0) 2) 2
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_022
  have c_023 := congrFun (congrFun (h 0) 2) 3
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_023
  have c_030 := congrFun (congrFun (h 0) 3) 0
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_030
  have c_031 := congrFun (congrFun (h 0) 3) 1
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_031
  have c_032 := congrFun (congrFun (h 0) 3) 2
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_032
  have c_033 := congrFun (congrFun (h 0) 3) 3
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_033
  have c_100 := congrFun (congrFun (h 1) 0) 0
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_100
  have c_101 := congrFun (congrFun (h 1) 0) 1
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_101
  have c_102 := congrFun (congrFun (h 1) 0) 2
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_102
  have c_103 := congrFun (congrFun (h 1) 0) 3
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_103
  have c_110 := congrFun (congrFun (h 1) 1) 0
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_110
  have c_111 := congrFun (congrFun (h 1) 1) 1
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_111
  have c_112 := congrFun (congrFun (h 1) 1) 2
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_112
  have c_113 := congrFun (congrFun (h 1) 1) 3
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_113
  have c_120 := congrFun (congrFun (h 1) 2) 0
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_120
  have c_121 := congrFun (congrFun (h 1) 2) 1
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_121
  have c_122 := congrFun (congrFun (h 1) 2) 2
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_122
  have c_123 := congrFun (congrFun (h 1) 2) 3
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_123
  have c_130 := congrFun (congrFun (h 1) 3) 0
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_130
  have c_131 := congrFun (congrFun (h 1) 3) 1
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_131
  have c_132 := congrFun (congrFun (h 1) 3) 2
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_132
  have c_133 := congrFun (congrFun (h 1) 3) 3
  simp [rho, Matrix.mul_apply, Fin.sum_univ_four] at c_133
  have h00 : S 0 0 = 0 ∨ S 0 0 = 1 := by
    generalize S 0 0 = a; revert a; decide
  rcases h00 with h00 | h00
  · left
    ext i l; fin_cases i <;> fin_cases l <;> simp <;> grind
  · right
    ext i l; fin_cases i <;> fin_cases l <;> simp <;> grind

set_option maxHeartbeats 4000000 in
theorem splitRigid_rho : SplitRigid rho := by
  intro ε β h0 hs h
  have e := fun j i l m => congrFun (h j i l) m
  have e_0000 := e 0 0 0 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0000
  have e_0001 := e 0 0 0 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0001
  have e_0002 := e 0 0 0 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0002
  have e_0003 := e 0 0 0 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0003
  have e_0010 := e 0 0 1 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0010
  have e_0011 := e 0 0 1 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0011
  have e_0012 := e 0 0 1 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0012
  have e_0013 := e 0 0 1 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0013
  have e_0020 := e 0 0 2 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0020
  have e_0021 := e 0 0 2 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0021
  have e_0022 := e 0 0 2 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0022
  have e_0023 := e 0 0 2 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0023
  have e_0030 := e 0 0 3 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0030
  have e_0031 := e 0 0 3 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0031
  have e_0032 := e 0 0 3 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0032
  have e_0033 := e 0 0 3 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0033
  have e_0100 := e 0 1 0 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0100
  have e_0101 := e 0 1 0 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0101
  have e_0102 := e 0 1 0 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0102
  have e_0103 := e 0 1 0 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0103
  have e_0110 := e 0 1 1 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0110
  have e_0111 := e 0 1 1 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0111
  have e_0112 := e 0 1 1 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0112
  have e_0113 := e 0 1 1 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0113
  have e_0120 := e 0 1 2 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0120
  have e_0121 := e 0 1 2 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0121
  have e_0122 := e 0 1 2 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0122
  have e_0123 := e 0 1 2 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0123
  have e_0130 := e 0 1 3 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0130
  have e_0131 := e 0 1 3 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0131
  have e_0132 := e 0 1 3 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0132
  have e_0133 := e 0 1 3 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0133
  have e_0200 := e 0 2 0 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0200
  have e_0201 := e 0 2 0 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0201
  have e_0202 := e 0 2 0 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0202
  have e_0203 := e 0 2 0 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0203
  have e_0210 := e 0 2 1 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0210
  have e_0211 := e 0 2 1 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0211
  have e_0212 := e 0 2 1 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0212
  have e_0213 := e 0 2 1 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0213
  have e_0220 := e 0 2 2 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0220
  have e_0221 := e 0 2 2 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0221
  have e_0222 := e 0 2 2 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0222
  have e_0223 := e 0 2 2 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0223
  have e_0230 := e 0 2 3 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0230
  have e_0231 := e 0 2 3 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0231
  have e_0232 := e 0 2 3 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0232
  have e_0233 := e 0 2 3 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0233
  have e_0300 := e 0 3 0 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0300
  have e_0301 := e 0 3 0 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0301
  have e_0302 := e 0 3 0 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0302
  have e_0303 := e 0 3 0 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0303
  have e_0310 := e 0 3 1 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0310
  have e_0311 := e 0 3 1 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0311
  have e_0312 := e 0 3 1 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0312
  have e_0313 := e 0 3 1 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0313
  have e_0320 := e 0 3 2 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0320
  have e_0321 := e 0 3 2 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0321
  have e_0322 := e 0 3 2 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0322
  have e_0323 := e 0 3 2 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0323
  have e_0330 := e 0 3 3 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0330
  have e_0331 := e 0 3 3 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0331
  have e_0332 := e 0 3 3 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0332
  have e_0333 := e 0 3 3 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_0333
  have e_1000 := e 1 0 0 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1000
  have e_1001 := e 1 0 0 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1001
  have e_1002 := e 1 0 0 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1002
  have e_1003 := e 1 0 0 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1003
  have e_1010 := e 1 0 1 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1010
  have e_1011 := e 1 0 1 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1011
  have e_1012 := e 1 0 1 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1012
  have e_1013 := e 1 0 1 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1013
  have e_1020 := e 1 0 2 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1020
  have e_1021 := e 1 0 2 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1021
  have e_1022 := e 1 0 2 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1022
  have e_1023 := e 1 0 2 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1023
  have e_1030 := e 1 0 3 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1030
  have e_1031 := e 1 0 3 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1031
  have e_1032 := e 1 0 3 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1032
  have e_1033 := e 1 0 3 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1033
  have e_1100 := e 1 1 0 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1100
  have e_1101 := e 1 1 0 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1101
  have e_1102 := e 1 1 0 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1102
  have e_1103 := e 1 1 0 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1103
  have e_1110 := e 1 1 1 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1110
  have e_1111 := e 1 1 1 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1111
  have e_1112 := e 1 1 1 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1112
  have e_1113 := e 1 1 1 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1113
  have e_1120 := e 1 1 2 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1120
  have e_1121 := e 1 1 2 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1121
  have e_1122 := e 1 1 2 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1122
  have e_1123 := e 1 1 2 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1123
  have e_1130 := e 1 1 3 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1130
  have e_1131 := e 1 1 3 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1131
  have e_1132 := e 1 1 3 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1132
  have e_1133 := e 1 1 3 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1133
  have e_1200 := e 1 2 0 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1200
  have e_1201 := e 1 2 0 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1201
  have e_1202 := e 1 2 0 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1202
  have e_1203 := e 1 2 0 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1203
  have e_1210 := e 1 2 1 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1210
  have e_1211 := e 1 2 1 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1211
  have e_1212 := e 1 2 1 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1212
  have e_1213 := e 1 2 1 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1213
  have e_1220 := e 1 2 2 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1220
  have e_1221 := e 1 2 2 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1221
  have e_1222 := e 1 2 2 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1222
  have e_1223 := e 1 2 2 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1223
  have e_1230 := e 1 2 3 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1230
  have e_1231 := e 1 2 3 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1231
  have e_1232 := e 1 2 3 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1232
  have e_1233 := e 1 2 3 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1233
  have e_1300 := e 1 3 0 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1300
  have e_1301 := e 1 3 0 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1301
  have e_1302 := e 1 3 0 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1302
  have e_1303 := e 1 3 0 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1303
  have e_1310 := e 1 3 1 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1310
  have e_1311 := e 1 3 1 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1311
  have e_1312 := e 1 3 1 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1312
  have e_1313 := e 1 3 1 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1313
  have e_1320 := e 1 3 2 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1320
  have e_1321 := e 1 3 2 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1321
  have e_1322 := e 1 3 2 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1322
  have e_1323 := e 1 3 2 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1323
  have e_1330 := e 1 3 3 0
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1330
  have e_1331 := e 1 3 3 1
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1331
  have e_1332 := e 1 3 3 2
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1332
  have e_1333 := e 1 3 3 3
  simp [rho, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.vecHead, Matrix.vecTail] at e_1333
  have z_00 := congrFun (h0 0) 0
  simp at z_00
  have z_01 := congrFun (h0 0) 1
  simp at z_01
  have z_02 := congrFun (h0 0) 2
  simp at z_02
  have z_03 := congrFun (h0 0) 3
  simp at z_03
  have z_10 := congrFun (h0 1) 0
  simp at z_10
  have z_11 := congrFun (h0 1) 1
  simp at z_11
  have z_12 := congrFun (h0 1) 2
  simp at z_12
  have z_13 := congrFun (h0 1) 3
  simp at z_13
  have z_20 := congrFun (h0 2) 0
  simp at z_20
  have z_21 := congrFun (h0 2) 1
  simp at z_21
  have z_22 := congrFun (h0 2) 2
  simp at z_22
  have z_23 := congrFun (h0 2) 3
  simp at z_23
  have z_30 := congrFun (h0 3) 0
  simp at z_30
  have z_31 := congrFun (h0 3) 1
  simp at z_31
  have z_32 := congrFun (h0 3) 2
  simp at z_32
  have z_33 := congrFun (h0 3) 3
  simp at z_33
  have s_010 := congrFun (hs 0 1) 0
  have s_011 := congrFun (hs 0 1) 1
  have s_012 := congrFun (hs 0 1) 2
  have s_013 := congrFun (hs 0 1) 3
  have s_020 := congrFun (hs 0 2) 0
  have s_021 := congrFun (hs 0 2) 1
  have s_022 := congrFun (hs 0 2) 2
  have s_023 := congrFun (hs 0 2) 3
  have s_030 := congrFun (hs 0 3) 0
  have s_031 := congrFun (hs 0 3) 1
  have s_032 := congrFun (hs 0 3) 2
  have s_033 := congrFun (hs 0 3) 3
  have s_120 := congrFun (hs 1 2) 0
  have s_121 := congrFun (hs 1 2) 1
  have s_122 := congrFun (hs 1 2) 2
  have s_123 := congrFun (hs 1 2) 3
  have s_130 := congrFun (hs 1 3) 0
  have s_131 := congrFun (hs 1 3) 1
  have s_132 := congrFun (hs 1 3) 2
  have s_133 := congrFun (hs 1 3) 3
  have s_230 := congrFun (hs 2 3) 0
  have s_231 := congrFun (hs 2 3) 1
  have s_232 := congrFun (hs 2 3) 2
  have s_233 := congrFun (hs 2 3) 3
  refine ⟨![β 0 1 1, β 1 2 2, β 2 3 3, β 3 0 0], ?_, ?_⟩
  · intro j i; fin_cases j <;> fin_cases i <;> simp [rho, Fin.sum_univ_four] <;> grind
  · intro i l; fin_cases i <;> fin_cases l <;> ext m <;> fin_cases m <;> simp <;> grind

set_option maxHeartbeats 4000000 in
theorem z4Rigid_kx_ky : Z4Rigid kx ky := by
  intro X Y hx hy hX hY hXY
  obtain ⟨A, rfl⟩ := exists_lift hx
  obtain ⟨B, rfl⟩ := exists_lift hy
  have c1 : (ZMod.cast (1 : ZMod 2) : ZMod 4) = 1 := by decide
  have X_00 := congrFun (congrFun hX 0) 0
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_00
  have X_01 := congrFun (congrFun hX 0) 1
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_01
  have X_02 := congrFun (congrFun hX 0) 2
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_02
  have X_03 := congrFun (congrFun hX 0) 3
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_03
  have X_10 := congrFun (congrFun hX 1) 0
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_10
  have X_11 := congrFun (congrFun hX 1) 1
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_11
  have X_12 := congrFun (congrFun hX 1) 2
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_12
  have X_13 := congrFun (congrFun hX 1) 3
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_13
  have X_20 := congrFun (congrFun hX 2) 0
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_20
  have X_21 := congrFun (congrFun hX 2) 1
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_21
  have X_22 := congrFun (congrFun hX 2) 2
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_22
  have X_23 := congrFun (congrFun hX 2) 3
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_23
  have X_30 := congrFun (congrFun hX 3) 0
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_30
  have X_31 := congrFun (congrFun hX 3) 1
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_31
  have X_32 := congrFun (congrFun hX 3) 2
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_32
  have X_33 := congrFun (congrFun hX 3) 3
  simp [c1, lift, kx, Matrix.mul_apply, Fin.sum_univ_four] at X_33
  have Y_00 := congrFun (congrFun hY 0) 0
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_00
  have Y_01 := congrFun (congrFun hY 0) 1
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_01
  have Y_02 := congrFun (congrFun hY 0) 2
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_02
  have Y_03 := congrFun (congrFun hY 0) 3
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_03
  have Y_10 := congrFun (congrFun hY 1) 0
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_10
  have Y_11 := congrFun (congrFun hY 1) 1
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_11
  have Y_12 := congrFun (congrFun hY 1) 2
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_12
  have Y_13 := congrFun (congrFun hY 1) 3
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_13
  have Y_20 := congrFun (congrFun hY 2) 0
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_20
  have Y_21 := congrFun (congrFun hY 2) 1
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_21
  have Y_22 := congrFun (congrFun hY 2) 2
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_22
  have Y_23 := congrFun (congrFun hY 2) 3
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_23
  have Y_30 := congrFun (congrFun hY 3) 0
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_30
  have Y_31 := congrFun (congrFun hY 3) 1
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_31
  have Y_32 := congrFun (congrFun hY 3) 2
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_32
  have Y_33 := congrFun (congrFun hY 3) 3
  simp [c1, lift, ky, Matrix.mul_apply, Fin.sum_univ_four] at Y_33
  have Z_00 := congrFun (congrFun hXY 0) 0
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_00
  have Z_01 := congrFun (congrFun hXY 0) 1
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_01
  have Z_02 := congrFun (congrFun hXY 0) 2
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_02
  have Z_03 := congrFun (congrFun hXY 0) 3
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_03
  have Z_10 := congrFun (congrFun hXY 1) 0
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_10
  have Z_11 := congrFun (congrFun hXY 1) 1
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_11
  have Z_12 := congrFun (congrFun hXY 1) 2
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_12
  have Z_13 := congrFun (congrFun hXY 1) 3
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_13
  have Z_20 := congrFun (congrFun hXY 2) 0
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_20
  have Z_21 := congrFun (congrFun hXY 2) 1
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_21
  have Z_22 := congrFun (congrFun hXY 2) 2
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_22
  have Z_23 := congrFun (congrFun hXY 2) 3
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_23
  have Z_30 := congrFun (congrFun hXY 3) 0
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_30
  have Z_31 := congrFun (congrFun hXY 3) 1
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_31
  have Z_32 := congrFun (congrFun hXY 3) 2
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_32
  have Z_33 := congrFun (congrFun hXY 3) 3
  simp [c1, lift, kx, ky, Matrix.mul_apply, Fin.sum_univ_four] at Z_33
  grind

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2
