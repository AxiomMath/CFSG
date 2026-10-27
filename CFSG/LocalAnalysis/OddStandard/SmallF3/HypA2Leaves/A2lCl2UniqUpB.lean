module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

private theorem cl24_ppd_le_sub {j e k ℓ : ℕ}
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (h : ℓ ∣ (3 ^ j) ^ e - 1)
    (hj : 0 < j) (he : 0 < e) : k ≤ j * e :=
  Nat.le_of_dvd (Nat.mul_pos hj he) (cl24_dvd_of_dvd_sub hk h)

private theorem cl24_ppd_le_add {j e k ℓ : ℕ}
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (h : ℓ ∣ (3 ^ j) ^ e + 1)
    (hj : 0 < j) (he : 0 < e) : k ≤ 2 * (j * e) :=
  Nat.le_of_dvd (by positivity) (cl24_dvd_of_dvd_add hk h)

private theorem cl24_triality_factor_dvd (q : ℕ) : q ^ 8 + q ^ 4 + 1 ∣ q ^ 12 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have h1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ hq
  have h : q ^ 12 - 1 = (q ^ 4 - 1) * (q ^ 8 + q ^ 4 + 1) := by
    zify [h1, h2]
    ring
  rw [h]
  exact dvd_mul_left _ _

theorem cl24_ppd_le_G2 {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .G2 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .G2 n (3 ^ j)) :
    k ≤ j * cl24E .G2 n := by
  have hj : 1 ≤ j := hadm.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  repeat rw [Nat.Prime.dvd_mul hℓ] at hd
  rcases hd with h | h
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 6)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 2)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))

theorem cl24_ppd_le_F4 {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .F4 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .F4 n (3 ^ j)) :
    k ≤ j * cl24E .F4 n := by
  have hj : 1 ≤ j := hadm.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  repeat rw [Nat.Prime.dvd_mul hℓ] at hd
  simp only [or_assoc] at hd
  rcases hd with h | h | h | h
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 12)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 8)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 6)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 2)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))

theorem cl24_ppd_le_E6 {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .E6 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .E6 n (3 ^ j)) :
    k ≤ j * cl24E .E6 n := by
  have hj : 1 ≤ j := hadm.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  repeat rw [Nat.Prime.dvd_mul hℓ] at hd
  simp only [or_assoc] at hd
  rcases hd with h | h | h | h | h | h
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 12)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 9)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 8)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 6)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 5)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 2)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))

theorem cl24_ppd_le_E7 {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .E7 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .E7 n (3 ^ j)) :
    k ≤ j * cl24E .E7 n := by
  have hj : 1 ≤ j := hadm.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  repeat rw [Nat.Prime.dvd_mul hℓ] at hd
  simp only [or_assoc] at hd
  rcases hd with h | h | h | h | h | h | h
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 18)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 14)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 12)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 10)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 8)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 6)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 2)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))

theorem cl24_ppd_le_E8 {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .E8 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .E8 n (3 ^ j)) :
    k ≤ j * cl24E .E8 n := by
  have hj : 1 ≤ j := hadm.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  repeat rw [Nat.Prime.dvd_mul hℓ] at hd
  simp only [or_assoc] at hd
  rcases hd with h | h | h | h | h | h | h | h
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 30)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 24)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 20)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 18)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 14)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 12)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 8)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 2)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))

theorem cl24_ppd_le_twistedE6 {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .twistedE6 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i)
    (hd : ℓ ∣ lieOrderCofactor .twistedE6 n (3 ^ j)) :
    k ≤ j * cl24E .twistedE6 n := by
  have hj : 1 ≤ j := hadm.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  repeat rw [Nat.Prime.dvd_mul hℓ] at hd
  simp only [or_assoc] at hd
  rcases hd with h | h | h | h | h | h
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 12)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_add hk h hj0 (by norm_num : 0 < 9)
    simp only [cl24E]
    calc k ≤ 2 * (j * 9) := hle
      _ = j * 18 := by ring
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 8)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 6)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_add hk h hj0 (by norm_num : 0 < 5)
    simp only [cl24E]
    calc k ≤ 2 * (j * 5) := hle
      _ = j * 10 := by ring
      _ ≤ j * 18 := Nat.mul_le_mul_left j (by norm_num)
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 2)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))

theorem cl24_ppd_le_trialityD4 {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i)
    (hd : ℓ ∣ lieOrderCofactor .trialityD4 n (3 ^ j)) :
    k ≤ j * cl24E .trialityD4 n := by
  have hj : 1 ≤ j := hadm.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  repeat rw [Nat.Prime.dvd_mul hℓ] at hd
  simp only [or_assoc] at hd
  rcases hd with h | h | h
  · have hdiv : ℓ ∣ (3 ^ j) ^ 12 - 1 := h.trans (cl24_triality_factor_dvd (3 ^ j))
    have hle := cl24_ppd_le_sub hk hdiv hj0 (by norm_num : 0 < 12)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 6)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))
  · have hle := cl24_ppd_le_sub hk h hj0 (by norm_num : 0 < 2)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))

theorem cl24_ppd_le_twistedG2 {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .twistedG2 n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i)
    (hd : ℓ ∣ lieOrderCofactor .twistedG2 n (3 ^ j)) :
    k ≤ j * cl24E .twistedG2 n := by
  have hj : 1 ≤ j := hadm.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  repeat rw [Nat.Prime.dvd_mul hℓ] at hd
  rcases hd with h | h
  · have hle := cl24_ppd_le_add hk h hj0 (by norm_num : 0 < 3)
    simp only [cl24E]
    calc k ≤ 2 * (j * 3) := hle
      _ = j * 6 := by ring
  · have hdiv : ℓ ∣ (3 ^ j) ^ 1 - 1 := by simpa using h
    have hle := cl24_ppd_le_sub hk hdiv hj0 (by norm_num : 0 < 1)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by norm_num))

end CFSG.OddStandard.SmallF3.HypA2Leaves
