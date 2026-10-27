module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

private lemma cl24_triality_factor (j : ℕ) :
    (3 ^ j) ^ 12 - 1 = ((3 ^ j) ^ 4 - 1) * ((3 ^ j) ^ 8 + (3 ^ j) ^ 4 + 1) := by
  have h12 : (3 ^ j) ^ 12 = ((3 ^ j) ^ 4) ^ 3 := by ring_nf
  have h8 : (3 ^ j) ^ 8 = ((3 ^ j) ^ 4) ^ 2 := by ring_nf
  rw [h12, h8]
  have h4 : 1 ≤ (3 ^ j) ^ 4 := Nat.one_le_pow _ _ (by positivity)
  have h3 : 1 ≤ ((3 ^ j) ^ 4) ^ 3 := Nat.one_le_pow _ _ (by positivity)
  apply Nat.cast_injective (R := ℤ)
  simp only [Nat.cast_sub h3, Nat.cast_sub h4, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow]
  ring

theorem cl24_ppd_dvd_G2 {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .G2 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .G2 n) :
    ℓ ∣ lieOrderCofactor .G2 n (3 ^ j) := by
  have hke' : k = j * 6 := by simpa [cl24E] using hke
  have h : ℓ ∣ (3 ^ j) ^ 6 - 1 := cl24_dvd_sub_of hk (by rw [hke'])
  simpa only [lieOrderCofactor] using h.mul_right ((3 ^ j) ^ 2 - 1)

theorem cl24_ppd_dvd_F4 {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .F4 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .F4 n) :
    ℓ ∣ lieOrderCofactor .F4 n (3 ^ j) := by
  have hke' : k = j * 12 := by simpa [cl24E] using hke
  have h : ℓ ∣ (3 ^ j) ^ 12 - 1 := cl24_dvd_sub_of hk (by rw [hke'])
  simpa only [lieOrderCofactor] using
    ((h.mul_right ((3 ^ j) ^ 8 - 1)).mul_right ((3 ^ j) ^ 6 - 1)).mul_right
      ((3 ^ j) ^ 2 - 1)

theorem cl24_ppd_dvd_E6 {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .E6 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .E6 n) :
    ℓ ∣ lieOrderCofactor .E6 n (3 ^ j) := by
  have hke' : k = j * 12 := by simpa [cl24E] using hke
  have h : ℓ ∣ (3 ^ j) ^ 12 - 1 := cl24_dvd_sub_of hk (by rw [hke'])
  simpa only [lieOrderCofactor] using
    ((((h.mul_right ((3 ^ j) ^ 9 - 1)).mul_right ((3 ^ j) ^ 8 - 1)).mul_right
      ((3 ^ j) ^ 6 - 1)).mul_right ((3 ^ j) ^ 5 - 1)).mul_right ((3 ^ j) ^ 2 - 1)

theorem cl24_ppd_dvd_E7 {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .E7 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .E7 n) :
    ℓ ∣ lieOrderCofactor .E7 n (3 ^ j) := by
  have hke' : k = j * 18 := by simpa [cl24E] using hke
  have h : ℓ ∣ (3 ^ j) ^ 18 - 1 := cl24_dvd_sub_of hk (by rw [hke'])
  simpa only [lieOrderCofactor] using
    (((((h.mul_right ((3 ^ j) ^ 14 - 1)).mul_right ((3 ^ j) ^ 12 - 1)).mul_right
      ((3 ^ j) ^ 10 - 1)).mul_right ((3 ^ j) ^ 8 - 1)).mul_right
      ((3 ^ j) ^ 6 - 1)).mul_right ((3 ^ j) ^ 2 - 1)

theorem cl24_ppd_dvd_E8 {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .E8 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .E8 n) :
    ℓ ∣ lieOrderCofactor .E8 n (3 ^ j) := by
  have hke' : k = j * 30 := by simpa [cl24E] using hke
  have h : ℓ ∣ (3 ^ j) ^ 30 - 1 := cl24_dvd_sub_of hk (by rw [hke'])
  simpa only [lieOrderCofactor] using
    ((((((h.mul_right ((3 ^ j) ^ 24 - 1)).mul_right ((3 ^ j) ^ 20 - 1)).mul_right
      ((3 ^ j) ^ 18 - 1)).mul_right ((3 ^ j) ^ 14 - 1)).mul_right
      ((3 ^ j) ^ 12 - 1)).mul_right ((3 ^ j) ^ 8 - 1)).mul_right ((3 ^ j) ^ 2 - 1)

theorem cl24_ppd_dvd_twistedE6 {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .twistedE6 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .twistedE6 n) :
    ℓ ∣ lieOrderCofactor .twistedE6 n (3 ^ j) := by
  have hke' : k = j * 18 := by simpa [cl24E] using hke
  have hke'' : k = 2 * (j * 9) := by rw [hke']; ring
  have h : ℓ ∣ (3 ^ j) ^ 9 + 1 :=
    cl24_dvd_add_of hℓ hk hke'' (by have := hadm.2.1; omega)
  simpa only [lieOrderCofactor] using
    ((((h.mul_left ((3 ^ j) ^ 12 - 1)).mul_right ((3 ^ j) ^ 8 - 1)).mul_right
      ((3 ^ j) ^ 6 - 1)).mul_right ((3 ^ j) ^ 5 + 1)).mul_right ((3 ^ j) ^ 2 - 1)

theorem cl24_ppd_dvd_twistedG2 {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .twistedG2 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .twistedG2 n) :
    ℓ ∣ lieOrderCofactor .twistedG2 n (3 ^ j) := by
  have hke' : k = j * 6 := by simpa [cl24E] using hke
  have hke'' : k = 2 * (j * 3) := by rw [hke']; ring
  have h : ℓ ∣ (3 ^ j) ^ 3 + 1 :=
    cl24_dvd_add_of hℓ hk hke'' (by have := hadm.2.1; omega)
  simpa only [lieOrderCofactor] using h.mul_right ((3 ^ j) - 1)

theorem cl24_ppd_dvd_trialityD4 {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .trialityD4 n) :
    ℓ ∣ lieOrderCofactor .trialityD4 n (3 ^ j) := by
  have hke' : k = j * 12 := by simpa [cl24E] using hke
  have h12 : ℓ ∣ (3 ^ j) ^ 12 - 1 := cl24_dvd_sub_of hk (by rw [hke'])
  rw [cl24_triality_factor j] at h12
  have hfac : ℓ ∣ (3 ^ j) ^ 8 + (3 ^ j) ^ 4 + 1 := by
    rcases (Nat.Prime.dvd_mul hℓ).1 h12 with h | h
    · exfalso
      have hk4 : k ∣ j * 4 := cl24_dvd_of_dvd_sub hk h
      have hj : 0 < j := by have := hadm.2.1; omega
      have hle : j * 12 ≤ j * 4 :=
        Nat.le_of_dvd (Nat.mul_pos hj (by norm_num)) (by rwa [hke'] at hk4)
      omega
    · exact h
  simpa only [lieOrderCofactor] using
    (hfac.mul_right ((3 ^ j) ^ 6 - 1)).mul_right ((3 ^ j) ^ 2 - 1)

end CFSG.OddStandard.SmallF3.HypA2Leaves
