module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

private theorem cl24_E_eq_two_N {τ : StatedLieTag} {n j : ℕ}
    (hadm : StatedLieAdmissible τ n 3 j) (h : cl24E τ n = 2 * lieSylowExponent τ n) :
    (τ = .PSL ∧ n = 2) ∨ (τ = .PSU ∧ n = 3) ∨ τ = .twistedG2 := by
  cases τ
  · left; refine ⟨rfl, ?_⟩
    have hn2 : 2 ≤ n := hadm.2.2.1
    have hn0 : 0 < n := by omega
    simp only [cl24E, lieSylowExponent] at h
    rw [cl24_tri n] at h
    have h' : n * 1 = n * (n - 1) := by rw [Nat.mul_one]; exact h
    have := Nat.mul_left_cancel hn0 h'
    omega
  · right; left; refine ⟨rfl, ?_⟩
    have hn3 : 3 ≤ n := hadm.2.2.1
    by_cases hEven : Even n
    · exfalso
      simp only [cl24E, lieSylowExponent, if_pos hEven] at h
      rw [cl24_tri n] at h
      have hnm1 : 0 < n - 1 := by omega
      have := Nat.mul_right_cancel hnm1 h
      omega
    · simp only [cl24E, lieSylowExponent, if_neg hEven] at h
      rw [cl24_tri n] at h
      have hn0 : 0 < n := by omega
      rw [mul_comm 2 n] at h
      have := Nat.mul_left_cancel hn0 h
      omega
  · exfalso
    have hn2 : 2 ≤ n := hadm.2.2.1
    have hn0 : 0 < n := by omega
    simp only [cl24E, lieSylowExponent] at h
    rw [pow_two] at h
    have h2 := Nat.mul_left_cancel (by norm_num : 0 < 2) h
    have h' : n * 1 = n * n := by rw [Nat.mul_one]; exact h2
    have := Nat.mul_left_cancel hn0 h'
    omega
  · exfalso
    have hn3 : 3 ≤ n := hadm.2.2.1
    have hn0 : 0 < n := by omega
    simp only [cl24E, lieSylowExponent] at h
    rw [pow_two] at h
    have h2 := Nat.mul_left_cancel (by norm_num : 0 < 2) h
    have h' : n * 1 = n * n := by rw [Nat.mul_one]; exact h2
    have := Nat.mul_left_cancel hn0 h'
    omega
  · exfalso
    have hn4 : 4 ≤ n := hadm.2.2
    have hnm1 : 0 < n - 1 := by omega
    simp only [cl24E, lieSylowExponent] at h
    have h2 := Nat.mul_left_cancel (by norm_num : 0 < 2) h
    have h' : (n - 1) * 1 = (n - 1) * n := by
      rw [Nat.mul_one]
      rw [mul_comm n (n - 1)] at h2
      exact h2
    have := Nat.mul_left_cancel hnm1 h'
    omega
  · exfalso
    have hn4 : 4 ≤ n := hadm.2.2
    have hn0 : 0 < n := by omega
    simp only [cl24E, lieSylowExponent] at h
    have h2 := Nat.mul_left_cancel (by norm_num : 0 < 2) h
    have h' : n * 1 = n * (n - 1) := by rw [Nat.mul_one]; exact h2
    have := Nat.mul_left_cancel hn0 h'
    omega
  · exfalso; simp only [cl24E, lieSylowExponent] at h; omega
  · exfalso; simp only [cl24E, lieSylowExponent] at h; omega
  · exfalso; simp only [cl24E, lieSylowExponent] at h; omega
  · exfalso; simp only [cl24E, lieSylowExponent] at h; omega
  · exfalso; simp only [cl24E, lieSylowExponent] at h; omega
  · exfalso; simp only [cl24E, lieSylowExponent] at h; omega
  · exfalso; simp only [cl24E, lieSylowExponent] at h; omega
  · exfalso; exact absurd hadm.2.2.2.1 (by norm_num)
  · right; right; rfl
  · exfalso; simp only [cl24E, lieSylowExponent] at h; omega
  · exfalso; exact absurd hadm.2.2.2.1 (by norm_num)

private theorem cl24_cube_sub_one (q : ℕ) (hq : 1 ≤ q) :
    q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  have h := geom_sum_mul_of_one_le hq 3
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [← h]
  ring

private theorem cl24_two_dvd_three_pow_sub_one (d : ℕ) : 2 ∣ 3 ^ d - 1 := by
  obtain ⟨k, hk⟩ := (show Odd (3 : ℕ) by norm_num).pow (n := d)
  exact ⟨k, by omega⟩

theorem cl24_twistedG2_small {τ' : StatedLieTag} {n' j d : ℕ}
    (hadm : StatedLieAdmissible .twistedG2 0 3 j) (hadm' : StatedLieAdmissible τ' n' 3 d)
    (hjd : j < d) (hN : lieSylowExponent .twistedG2 0 * j = lieSylowExponent τ' n' * d)
    (hE : j * cl24E .twistedG2 0 = d * cl24E τ' n')
    (hC : lieOrderCofactor .twistedG2 0 (3 ^ j) * lieOrderDivisor τ' n' (3 ^ d) =
      lieOrderCofactor τ' n' (3 ^ d) * lieOrderDivisor .twistedG2 0 (3 ^ j)) : False := by
  have hj : 0 < j := by have := hadm.2.1; omega
  have hd : 0 < d := by have := hadm'.2.1; omega
  have hEN : cl24E τ' n' = 2 * lieSylowExponent τ' n' := by
    have h6 : cl24E .twistedG2 0 = 6 := rfl
    have h3 : lieSylowExponent .twistedG2 0 = 3 := rfl
    have hmain : d * cl24E τ' n' = d * (2 * lieSylowExponent τ' n') := by
      rw [h6] at hE
      rw [h3] at hN
      nlinarith [hE, hN]
    exact Nat.eq_of_mul_eq_mul_left hd hmain
  rcases cl24_E_eq_two_N hadm' hEN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
  ·
    have hd_eq : d = 3 * j := by
      simp only [lieSylowExponent] at hN
      omega
    subst d
    have hcofG : lieOrderCofactor .twistedG2 0 (3 ^ j) = ((3 ^ j) ^ 3 + 1) * (3 ^ j - 1) := by
      simp [lieOrderCofactor]
    have hcofP : lieOrderCofactor .PSL 2 (3 ^ (3 * j)) = (3 ^ (3 * j)) ^ 2 - 1 := by
      simp [lieOrderCofactor]
    have hdivP : lieOrderDivisor .PSL 2 (3 ^ (3 * j)) = 2 := by
      simp only [lieOrderDivisor]
      exact Nat.gcd_eq_left (cl24_two_dvd_three_pow_sub_one (3 * j))
    have hdivG : lieOrderDivisor .twistedG2 0 (3 ^ j) = 1 := rfl
    rw [hcofG, hcofP, hdivP, hdivG, mul_one] at hC
    rw [show 3 ^ (3 * j) = (3 ^ j) ^ 3 by rw [pow_mul']] at hC
    have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    have hq31 : 0 < (3 ^ j) ^ 3 + 1 := by positivity
    have h3j : 3 ≤ 3 ^ j := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq1 : 0 < 3 ^ j - 1 := by omega
    have hsq : ((3 ^ j) ^ 3) ^ 2 - 1 = ((3 ^ j) ^ 3 + 1) * ((3 ^ j) ^ 3 - 1) := by
      simpa using Nat.sq_sub_sq ((3 ^ j) ^ 3) 1
    rw [hsq, mul_assoc] at hC
    have h3 := Nat.mul_left_cancel hq31 hC
    have hcube := cl24_cube_sub_one (3 ^ j) h1
    rw [hcube] at h3
    have h4 := Nat.mul_left_cancel hq1 h3
    nlinarith
  ·
    simp only [lieSylowExponent] at hN
    omega
  ·
    simp only [lieSylowExponent] at hN
    omega

theorem cl24_twistedG2_large {τ : StatedLieTag} {n j d : ℕ}
    (hadm : StatedLieAdmissible τ n 3 j) (hadm' : StatedLieAdmissible .twistedG2 0 3 d)
    (hjd : j < d) (hN : lieSylowExponent τ n * j = lieSylowExponent .twistedG2 0 * d)
    (hE : j * cl24E τ n = d * cl24E .twistedG2 0) : False := by
  have hj : 0 < j := by have := hadm.2.1; omega
  have hEN : cl24E τ n = 2 * lieSylowExponent τ n := by
    have h6 : cl24E .twistedG2 0 = 6 := rfl
    have h3 : lieSylowExponent .twistedG2 0 = 3 := rfl
    have hmain : j * cl24E τ n = j * (2 * lieSylowExponent τ n) := by
      rw [h6] at hE
      rw [h3] at hN
      nlinarith [hE, hN]
    exact Nat.eq_of_mul_eq_mul_left hj hmain
  rcases cl24_E_eq_two_N hadm hEN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
  · simp only [lieSylowExponent] at hN; omega
  · simp only [lieSylowExponent] at hN; omega
  · simp only [lieSylowExponent] at hN; omega

end CFSG.OddStandard.SmallF3.HypA2Leaves
