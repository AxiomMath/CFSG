module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

private theorem cl24_cofMod_aux {j R : ℕ} (hj : 1 ≤ j) (hR : Cl24PM j (R : ℤ)) :
    Cl24CofMod (R * ((3 ^ j) ^ 2 - 1)) j := by
  rw [mul_comm]
  exact cl24CofMod_of_mul hj hR

private theorem cl24PM_triality {j : ℕ} (hj : 1 ≤ j) :
    Cl24PM j (((3 ^ j) ^ 8 + (3 ^ j) ^ 4 + 1 : ℕ) : ℤ) := by
  refine ⟨1, Or.inl rfl, ?_⟩
  have h8 : (((3 ^ j) ^ 8 : ℕ) : ℤ) ≡ 0 [ZMOD 3 ^ (2 * j + 1)] := by
    rw [Int.modEq_zero_iff_dvd]
    have : 3 ^ (2 * j + 1) ∣ (3 ^ j) ^ 8 := by
      rw [← pow_mul]
      exact pow_dvd_pow 3 (by nlinarith)
    exact_mod_cast this
  have h4 : (((3 ^ j) ^ 4 : ℕ) : ℤ) ≡ 0 [ZMOD 3 ^ (2 * j + 1)] := by
    rw [Int.modEq_zero_iff_dvd]
    have : 3 ^ (2 * j + 1) ∣ (3 ^ j) ^ 4 := by
      rw [← pow_mul]
      exact pow_dvd_pow 3 (by nlinarith)
    exact_mod_cast this
  push_cast
  simpa using (h8.add h4).add_right 1

theorem cl24_cofMod_G2 {n j : ℕ} (hadm : StatedLieAdmissible .G2 n 3 j) :
    Cl24CofMod (lieOrderCofactor .G2 n (3 ^ j)) j := by
  have hj : 1 ≤ j := hadm.2.1
  simp only [lieOrderCofactor]
  refine cl24_cofMod_aux hj ?_
  exact cl24PM_pow_sub (e := 6) hj (by norm_num)

theorem cl24_cofMod_F4 {n j : ℕ} (hadm : StatedLieAdmissible .F4 n 3 j) :
    Cl24CofMod (lieOrderCofactor .F4 n (3 ^ j)) j := by
  have hj : 1 ≤ j := hadm.2.1
  simp only [lieOrderCofactor]
  refine cl24_cofMod_aux hj ?_
  simp only [Nat.cast_mul]
  exact cl24PM_mul (cl24PM_mul (cl24PM_pow_sub (e := 12) hj (by norm_num))
    (cl24PM_pow_sub (e := 8) hj (by norm_num))) (cl24PM_pow_sub (e := 6) hj (by norm_num))

theorem cl24_cofMod_E6 {n j : ℕ} (hadm : StatedLieAdmissible .E6 n 3 j) :
    Cl24CofMod (lieOrderCofactor .E6 n (3 ^ j)) j := by
  have hj : 1 ≤ j := hadm.2.1
  simp only [lieOrderCofactor]
  refine cl24_cofMod_aux hj ?_
  simp only [Nat.cast_mul]
  exact cl24PM_mul (cl24PM_mul (cl24PM_mul (cl24PM_mul
    (cl24PM_pow_sub (e := 12) hj (by norm_num))
    (cl24PM_pow_sub (e := 9) hj (by norm_num)))
    (cl24PM_pow_sub (e := 8) hj (by norm_num)))
    (cl24PM_pow_sub (e := 6) hj (by norm_num)))
    (cl24PM_pow_sub (e := 5) hj (by norm_num))

theorem cl24_cofMod_E7 {n j : ℕ} (hadm : StatedLieAdmissible .E7 n 3 j) :
    Cl24CofMod (lieOrderCofactor .E7 n (3 ^ j)) j := by
  have hj : 1 ≤ j := hadm.2.1
  simp only [lieOrderCofactor]
  refine cl24_cofMod_aux hj ?_
  simp only [Nat.cast_mul]
  exact cl24PM_mul (cl24PM_mul (cl24PM_mul (cl24PM_mul (cl24PM_mul
    (cl24PM_pow_sub (e := 18) hj (by norm_num))
    (cl24PM_pow_sub (e := 14) hj (by norm_num)))
    (cl24PM_pow_sub (e := 12) hj (by norm_num)))
    (cl24PM_pow_sub (e := 10) hj (by norm_num)))
    (cl24PM_pow_sub (e := 8) hj (by norm_num)))
    (cl24PM_pow_sub (e := 6) hj (by norm_num))

theorem cl24_cofMod_E8 {n j : ℕ} (hadm : StatedLieAdmissible .E8 n 3 j) :
    Cl24CofMod (lieOrderCofactor .E8 n (3 ^ j)) j := by
  have hj : 1 ≤ j := hadm.2.1
  simp only [lieOrderCofactor]
  refine cl24_cofMod_aux hj ?_
  simp only [Nat.cast_mul]
  exact cl24PM_mul (cl24PM_mul (cl24PM_mul (cl24PM_mul (cl24PM_mul (cl24PM_mul
    (cl24PM_pow_sub (e := 30) hj (by norm_num))
    (cl24PM_pow_sub (e := 24) hj (by norm_num)))
    (cl24PM_pow_sub (e := 20) hj (by norm_num)))
    (cl24PM_pow_sub (e := 18) hj (by norm_num)))
    (cl24PM_pow_sub (e := 14) hj (by norm_num)))
    (cl24PM_pow_sub (e := 12) hj (by norm_num)))
    (cl24PM_pow_sub (e := 8) hj (by norm_num))

theorem cl24_cofMod_twistedE6 {n j : ℕ} (hadm : StatedLieAdmissible .twistedE6 n 3 j) :
    Cl24CofMod (lieOrderCofactor .twistedE6 n (3 ^ j)) j := by
  have hj : 1 ≤ j := hadm.2.1
  simp only [lieOrderCofactor]
  refine cl24_cofMod_aux hj ?_
  simp only [Nat.cast_mul]
  exact cl24PM_mul (cl24PM_mul (cl24PM_mul (cl24PM_mul
    (cl24PM_pow_sub (e := 12) hj (by norm_num))
    (cl24PM_pow_add (e := 9) hj (by norm_num)))
    (cl24PM_pow_sub (e := 8) hj (by norm_num)))
    (cl24PM_pow_sub (e := 6) hj (by norm_num)))
    (cl24PM_pow_add (e := 5) hj (by norm_num))

theorem cl24_cofMod_trialityD4 {n j : ℕ} (hadm : StatedLieAdmissible .trialityD4 n 3 j) :
    Cl24CofMod (lieOrderCofactor .trialityD4 n (3 ^ j)) j := by
  have hj : 1 ≤ j := hadm.2.1
  simp only [lieOrderCofactor]
  refine cl24_cofMod_aux hj ?_
  simp only [Nat.cast_mul]
  exact cl24PM_mul (cl24PM_triality hj) (cl24PM_pow_sub (e := 6) hj (by norm_num))

end CFSG.OddStandard.SmallF3.HypA2Leaves
