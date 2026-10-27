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

theorem cl24_ppd_le_PSL {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .PSL n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .PSL n (3 ^ j)) :
    k ≤ j * cl24E .PSL n := by
  have hj : 1 ≤ j := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  obtain ⟨i, hi, hdiv⟩ := Prime.exists_mem_finset_dvd hℓ.prime hd
  simp only [Finset.mem_Icc] at hi
  obtain ⟨hi2, hin⟩ := hi
  have hle := cl24_ppd_le_sub hk hdiv hj0 (by omega : 0 < i)
  simp only [cl24E]
  exact hle.trans (Nat.mul_le_mul_left j hin)

theorem cl24_ppd_le_PSU {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .PSU n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .PSU n (3 ^ j)) :
    k ≤ j * cl24E .PSU n := by
  have hj : 1 ≤ j := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  obtain ⟨i, hi, hdiv⟩ := Prime.exists_mem_finset_dvd hℓ.prime hd
  simp only [Finset.mem_Icc] at hi
  obtain ⟨hi2, hin⟩ := hi
  have hi0 : 0 < i := by omega
  have hE : i ≤ cl24E .PSU n := by
    simp only [cl24E]
    by_cases hn2 : Even n
    · rw [if_pos hn2]; omega
    · rw [if_neg hn2]; omega
  by_cases hie : Even i
  · have hdiv' : ℓ ∣ (3 ^ j) ^ i - 1 := by simpa [hie] using hdiv
    exact (cl24_ppd_le_sub hk hdiv' hj0 hi0).trans (Nat.mul_le_mul_left j hE)
  · have hdiv' : ℓ ∣ (3 ^ j) ^ i + 1 := by simpa [hie] using hdiv
    have hle := cl24_ppd_le_add hk hdiv' hj0 hi0
    have h2E : 2 * i ≤ cl24E .PSU n := by
      simp only [cl24E]
      by_cases hn2 : Even n
      · rw [if_pos hn2]
        have hilt : i < n := by
          by_contra h
          have hge : n ≤ i := le_of_not_gt h
          have hieq : i = n := le_antisymm hin hge
          exact hie (hieq.symm ▸ hn2)
        exact Nat.mul_le_mul_left 2 (Nat.le_pred_of_lt hilt)
      · rw [if_neg hn2]; omega
    have hrew : 2 * (j * i) = j * (2 * i) := by ring
    rw [hrew] at hle
    exact hle.trans (Nat.mul_le_mul_left j h2E)

theorem cl24_ppd_le_PSp {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .PSp n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .PSp n (3 ^ j)) :
    k ≤ j * cl24E .PSp n := by
  have hj : 1 ≤ j := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  obtain ⟨i, hi, hdiv⟩ := Prime.exists_mem_finset_dvd hℓ.prime hd
  simp only [Finset.mem_Icc] at hi
  obtain ⟨hi1, hin⟩ := hi
  have hle := cl24_ppd_le_sub hk hdiv hj0 (by omega : 0 < 2 * i)
  simp only [cl24E]
  exact hle.trans (Nat.mul_le_mul_left j (by omega))

theorem cl24_ppd_le_POmegaOdd {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .POmegaOdd n (3 ^ j)) :
    k ≤ j * cl24E .POmegaOdd n := by
  have hj : 1 ≤ j := hadm.2.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  obtain ⟨i, hi, hdiv⟩ := Prime.exists_mem_finset_dvd hℓ.prime hd
  simp only [Finset.mem_Icc] at hi
  obtain ⟨hi1, hin⟩ := hi
  have hle := cl24_ppd_le_sub hk hdiv hj0 (by omega : 0 < 2 * i)
  simp only [cl24E]
  exact hle.trans (Nat.mul_le_mul_left j (by omega))

theorem cl24_ppd_le_POmegaPlus {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .POmegaPlus n (3 ^ j)) :
    k ≤ j * cl24E .POmegaPlus n := by
  have hj : 1 ≤ j := hadm.2.1
  have hn : 4 ≤ n := hadm.2.2
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  rcases (Nat.Prime.dvd_mul hℓ).1 hd with hd1 | hd2
  · have hle := cl24_ppd_le_sub hk hd1 hj0 (by omega : 0 < n)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by omega))
  · obtain ⟨i, hi, hdiv⟩ := Prime.exists_mem_finset_dvd hℓ.prime hd2
    simp only [Finset.mem_Icc] at hi
    obtain ⟨hi1, hin⟩ := hi
    have hle := cl24_ppd_le_sub hk hdiv hj0 (by omega : 0 < 2 * i)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by omega))

theorem cl24_ppd_le_POmegaMinus {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hd : ℓ ∣ lieOrderCofactor .POmegaMinus n (3 ^ j)) :
    k ≤ j * cl24E .POmegaMinus n := by
  have hj : 1 ≤ j := hadm.2.1
  have hn : 4 ≤ n := hadm.2.2
  have hj0 : 0 < j := by omega
  simp only [lieOrderCofactor] at hd
  rcases (Nat.Prime.dvd_mul hℓ).1 hd with hd1 | hd2
  · have hle := cl24_ppd_le_add hk hd1 hj0 (by omega : 0 < n)
    simp only [cl24E]
    calc k ≤ 2 * (j * n) := hle
      _ = j * (2 * n) := by ring
  · obtain ⟨i, hi, hdiv⟩ := Prime.exists_mem_finset_dvd hℓ.prime hd2
    simp only [Finset.mem_Icc] at hi
    obtain ⟨hi1, hin⟩ := hi
    have hle := cl24_ppd_le_sub hk hdiv hj0 (by omega : 0 < 2 * i)
    simp only [cl24E]
    exact hle.trans (Nat.mul_le_mul_left j (by omega))

end CFSG.OddStandard.SmallF3.HypA2Leaves
