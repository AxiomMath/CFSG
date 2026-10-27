module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

theorem cl24_ppd_dvd_PSL {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .PSL n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .PSL n) :
    ℓ ∣ lieOrderCofactor .PSL n (3 ^ j) := by
  have hn : 2 ≤ n := hadm.2.2.1
  have hfac : ℓ ∣ (3 ^ j) ^ n - 1 := by
    apply cl24_dvd_sub_of hk
    rw [hke]
    exact dvd_rfl
  simp only [lieOrderCofactor]
  exact dvd_trans hfac (Finset.dvd_prod_of_mem (fun i => (3 ^ j) ^ i - 1) (by
    simp only [Finset.mem_Icc]; exact ⟨hn, le_rfl⟩))

theorem cl24_ppd_dvd_PSU {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .PSU n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .PSU n) :
    ℓ ∣ lieOrderCofactor .PSU n (3 ^ j) := by
  have hn : 3 ≤ n := hadm.2.2.1
  have hj : 1 ≤ j := hadm.2.1
  simp only [lieOrderCofactor]
  by_cases hn2 : Even n
  · have hn4 : 4 ≤ n := by
      have h2 : n % 2 = 0 := Nat.even_iff.mp hn2
      omega
    have hodd : ¬ Even (n - 1) := by
      intro h
      have h1 : (n - 1) % 2 = 0 := Nat.even_iff.mp h
      have h2 : n % 2 = 0 := Nat.even_iff.mp hn2
      omega
    have hfac : ℓ ∣ (3 ^ j) ^ (n - 1) + 1 := by
      apply cl24_dvd_add_of hℓ hk
      · rw [hke]; simp only [cl24E, if_pos hn2]; ring
      · exact Nat.mul_pos (by omega) (by omega)
    have hf : ℓ ∣ (if Even (n - 1) then (3 ^ j) ^ (n - 1) - 1
        else (3 ^ j) ^ (n - 1) + 1) := by
      rw [if_neg hodd]; exact hfac
    exact dvd_trans hf (Finset.dvd_prod_of_mem
      (fun i => if Even i then (3 ^ j) ^ i - 1 else (3 ^ j) ^ i + 1) (by
        simp only [Finset.mem_Icc]; exact ⟨by omega, by omega⟩))
  · have hfac : ℓ ∣ (3 ^ j) ^ n + 1 := by
      apply cl24_dvd_add_of hℓ hk
      · rw [hke]; simp only [cl24E, if_neg hn2]; ring
      · exact Nat.mul_pos (by omega) (by omega)
    have hf : ℓ ∣ (if Even n then (3 ^ j) ^ n - 1 else (3 ^ j) ^ n + 1) := by
      rw [if_neg hn2]; exact hfac
    exact dvd_trans hf (Finset.dvd_prod_of_mem
      (fun i => if Even i then (3 ^ j) ^ i - 1 else (3 ^ j) ^ i + 1) (by
        simp only [Finset.mem_Icc]; exact ⟨by omega, by omega⟩))

theorem cl24_ppd_dvd_PSp {n j k ℓ : ℕ} (hadm : StatedLieAdmissible .PSp n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .PSp n) :
    ℓ ∣ lieOrderCofactor .PSp n (3 ^ j) := by
  have hn : 2 ≤ n := hadm.2.2.1
  have hfac : ℓ ∣ (3 ^ j) ^ (2 * n) - 1 := by
    apply cl24_dvd_sub_of hk
    rw [hke]
    exact dvd_rfl
  simp only [lieOrderCofactor]
  exact dvd_trans hfac (Finset.dvd_prod_of_mem (fun i => (3 ^ j) ^ (2 * i) - 1) (by
    simp only [Finset.mem_Icc]; exact ⟨by omega, le_rfl⟩))

theorem cl24_ppd_dvd_POmegaOdd {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .POmegaOdd n) :
    ℓ ∣ lieOrderCofactor .POmegaOdd n (3 ^ j) := by
  have hn : 3 ≤ n := hadm.2.2.1
  have hfac : ℓ ∣ (3 ^ j) ^ (2 * n) - 1 := by
    apply cl24_dvd_sub_of hk
    rw [hke]
    exact dvd_rfl
  simp only [lieOrderCofactor]
  exact dvd_trans hfac (Finset.dvd_prod_of_mem (fun i => (3 ^ j) ^ (2 * i) - 1) (by
    simp only [Finset.mem_Icc]; exact ⟨by omega, le_rfl⟩))

theorem cl24_ppd_dvd_POmegaPlus {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .POmegaPlus n) :
    ℓ ∣ lieOrderCofactor .POmegaPlus n (3 ^ j) := by
  have hn : 4 ≤ n := hadm.2.2
  have hfac : ℓ ∣ (3 ^ j) ^ (2 * (n - 1)) - 1 := by
    apply cl24_dvd_sub_of hk
    rw [hke]
    exact dvd_rfl
  simp only [lieOrderCofactor]
  refine dvd_trans hfac ?_
  exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun i => (3 ^ j) ^ (2 * i) - 1) (by
    simp only [Finset.mem_Icc]; exact ⟨by omega, le_rfl⟩)) _

theorem cl24_ppd_dvd_POmegaMinus {n j k ℓ : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n 3 j) (hℓ : ℓ.Prime)
    (hk : ∀ i : ℕ, ℓ ∣ 3 ^ i - 1 ↔ k ∣ i) (hke : k = j * cl24E .POmegaMinus n) :
    ℓ ∣ lieOrderCofactor .POmegaMinus n (3 ^ j) := by
  have hn : 4 ≤ n := hadm.2.2
  have hj : 1 ≤ j := hadm.2.1
  have hfac : ℓ ∣ (3 ^ j) ^ n + 1 := by
    apply cl24_dvd_add_of hℓ hk
    · rw [hke]; simp only [cl24E]; ring
    · exact Nat.mul_pos (by omega) (by omega)
  simp only [lieOrderCofactor]
  exact dvd_mul_of_dvd_left hfac _

end CFSG.OddStandard.SmallF3.HypA2Leaves
