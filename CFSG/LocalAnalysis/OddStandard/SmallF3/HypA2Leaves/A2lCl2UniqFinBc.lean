module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDiv

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

private theorem cl24_PSU_E_pos (n' : ℕ) (hn' : 3 ≤ n') : 0 < cl24E .PSU n' := by
  simp only [cl24E]
  split_ifs <;> omega

private theorem cl24_PSU_rel_odd {N E n' : ℕ} (hn' : 0 < n')
    (h : N * (2 * n') = n' * (n' - 1) / 2 * E) : 4 * N = (n' - 1) * E := by
  have ht := cl24_tri n'
  have hc : (4 * N) * n' = ((n' - 1) * E) * n' := by nlinarith only [h, ht]
  exact Nat.eq_of_mul_eq_mul_right hn' hc

private theorem cl24_PSU_rel_even {N E n' : ℕ} (hn' : 1 < n')
    (h : N * (2 * (n' - 1)) = n' * (n' - 1) / 2 * E) : 4 * N = n' * E := by
  have ht := cl24_tri n'
  have hm : 0 < n' - 1 := by omega
  have hc : (4 * N) * (n' - 1) = (n' * E) * (n' - 1) := by nlinarith only [h, ht]
  exact Nat.eq_of_mul_eq_mul_right hm hc

private theorem cl24_finPSU_PSL {n n' j d : ℕ}
    (hadm : StatedLieAdmissible .PSL n 3 j) (hadm' : StatedLieAdmissible .PSU n' 3 d)
    (hjd : j < d)
    (hN : lieSylowExponent .PSL n * j = lieSylowExponent .PSU n' * d)
    (hE : j * cl24E .PSL n = d * cl24E .PSU n') : False := by
  obtain ⟨-, hj1, hn2, -⟩ := hadm
  obtain ⟨-, hd1, hn'3, -⟩ := hadm'
  have hj : 0 < j := by omega
  have hd : 0 < d := by omega
  have hEpos : 0 < cl24E .PSU n' := cl24_PSU_E_pos n' hn'3
  have hElt := cl24_E_lt hj hjd hE hEpos
  have hEltn : (if Even n' then 2 * (n' - 1) else 2 * n') < n := by
    simpa only [cl24E] using hElt
  have hcross := cl24_cross_NE hj hd hN hE
  simp only [lieSylowExponent, cl24E] at hcross
  by_cases hn'ev : Even n'
  · rw [if_pos hn'ev] at hcross
    have h4 := cl24_PSU_rel_even (by omega : 1 < n') hcross
    have hrel : 2 * (n - 1) = n' := by
      have ht := cl24_tri n
      have hc : (2 * (n - 1)) * n = n' * n := by nlinarith only [h4, ht]
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < n) hc
    rw [if_pos hn'ev, ← hrel] at hEltn
    omega
  · rw [if_neg hn'ev] at hcross
    have h4 := cl24_PSU_rel_odd (by omega : 0 < n') hcross
    have hrel : 2 * (n - 1) = n' - 1 := by
      have ht := cl24_tri n
      have hc : (2 * (n - 1)) * n = (n' - 1) * n := by nlinarith only [h4, ht]
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < n) hc
    have hn'val : n' = 2 * (n - 1) + 1 := by omega
    rw [if_neg hn'ev, hn'val] at hEltn
    omega

private theorem cl24_finPSU_sq2n {n n' j d : ℕ} (hj1 : 1 ≤ j) (hn2 : 2 ≤ n)
    (hadm' : StatedLieAdmissible .PSU n' 3 d) (hjd : j < d)
    (hN : n ^ 2 * j = lieSylowExponent .PSU n' * d)
    (hE : j * (2 * n) = d * cl24E .PSU n') : False := by
  obtain ⟨-, hd1, hn'3, -⟩ := hadm'
  have hj : 0 < j := by omega
  have hd : 0 < d := by omega
  have hEpos : 0 < cl24E .PSU n' := cl24_PSU_E_pos n' hn'3
  have hElt := cl24_E_lt hj hjd hE hEpos
  have hEltn : (if Even n' then 2 * (n' - 1) else 2 * n') < 2 * n := by
    simpa only [cl24E] using hElt
  have hcross := cl24_cross_NE hj hd hN hE
  simp only [lieSylowExponent, cl24E] at hcross
  by_cases hn'ev : Even n'
  · rw [if_pos hn'ev] at hcross
    have h4 := cl24_PSU_rel_even (by omega : 1 < n') hcross
    have hrel : 2 * n = n' := by
      have hc : (2 * n) * (2 * n) = n' * (2 * n) := by nlinarith only [h4]
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n) hc
    rw [if_pos hn'ev, ← hrel] at hEltn
    omega
  · rw [if_neg hn'ev] at hcross
    have h4 := cl24_PSU_rel_odd (by omega : 0 < n') hcross
    have hrel : 2 * n = n' - 1 := by
      have hc : (2 * n) * (2 * n) = (n' - 1) * (2 * n) := by nlinarith only [h4]
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n) hc
    have hn'val : n' = 2 * n + 1 := by omega
    rw [if_neg hn'ev, hn'val] at hEltn
    omega

private theorem cl24_finPSU_PSp {n n' j d : ℕ}
    (hadm : StatedLieAdmissible .PSp n 3 j) (hadm' : StatedLieAdmissible .PSU n' 3 d)
    (hjd : j < d)
    (hN : lieSylowExponent .PSp n * j = lieSylowExponent .PSU n' * d)
    (hE : j * cl24E .PSp n = d * cl24E .PSU n') : False := by
  obtain ⟨-, hj1, hn2, -⟩ := hadm
  exact cl24_finPSU_sq2n hj1 hn2 hadm' hjd hN hE

private theorem cl24_finPSU_POmegaOdd {n n' j d : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n 3 j) (hadm' : StatedLieAdmissible .PSU n' 3 d)
    (hjd : j < d)
    (hN : lieSylowExponent .POmegaOdd n * j = lieSylowExponent .PSU n' * d)
    (hE : j * cl24E .POmegaOdd n = d * cl24E .PSU n') : False := by
  obtain ⟨-, hj1, hn3, -⟩ := hadm
  exact cl24_finPSU_sq2n hj1 (by omega : 2 ≤ n) hadm' hjd hN hE

private theorem cl24_finPSU_POmegaPlus {n n' j d : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n 3 j) (hadm' : StatedLieAdmissible .PSU n' 3 d)
    (hjd : j < d)
    (hN : lieSylowExponent .POmegaPlus n * j = lieSylowExponent .PSU n' * d)
    (hE : j * cl24E .POmegaPlus n = d * cl24E .PSU n') : False := by
  obtain ⟨-, hj1, hn4⟩ := hadm
  obtain ⟨-, hd1, hn'3, -⟩ := hadm'
  have hj : 0 < j := by omega
  have hd : 0 < d := by omega
  have hEpos : 0 < cl24E .PSU n' := cl24_PSU_E_pos n' hn'3
  have hElt := cl24_E_lt hj hjd hE hEpos
  have hEltn : (if Even n' then 2 * (n' - 1) else 2 * n') < 2 * (n - 1) := by
    simpa only [cl24E] using hElt
  have hcross := cl24_cross_NE hj hd hN hE
  simp only [lieSylowExponent, cl24E] at hcross
  by_cases hn'ev : Even n'
  · rw [if_pos hn'ev] at hcross
    have h4 := cl24_PSU_rel_even (by omega : 1 < n') hcross
    have hrel : 2 * n = n' := by
      have hc : (2 * n) * (2 * (n - 1)) = n' * (2 * (n - 1)) := by nlinarith only [h4]
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * (n - 1)) hc
    rw [if_pos hn'ev, ← hrel] at hEltn
    omega
  · rw [if_neg hn'ev] at hcross
    have h4 := cl24_PSU_rel_odd (by omega : 0 < n') hcross
    have hrel : 2 * n = n' - 1 := by
      have hc : (2 * n) * (2 * (n - 1)) = (n' - 1) * (2 * (n - 1)) := by nlinarith only [h4]
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * (n - 1)) hc
    have hn'val : n' = 2 * n + 1 := by omega
    rw [if_neg hn'ev, hn'val] at hEltn
    omega

private theorem cl24_finPSU_POmegaMinus {n n' j d : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n 3 j) (hadm' : StatedLieAdmissible .PSU n' 3 d)
    (hjd : j < d)
    (hN : lieSylowExponent .POmegaMinus n * j = lieSylowExponent .PSU n' * d)
    (hE : j * cl24E .POmegaMinus n = d * cl24E .PSU n') : False := by
  obtain ⟨-, hj1, hn4⟩ := hadm
  obtain ⟨-, hd1, hn'3, -⟩ := hadm'
  have hj : 0 < j := by omega
  have hd : 0 < d := by omega
  have hEpos : 0 < cl24E .PSU n' := cl24_PSU_E_pos n' hn'3
  have hElt := cl24_E_lt hj hjd hE hEpos
  have hEltn : (if Even n' then 2 * (n' - 1) else 2 * n') < 2 * n := by
    simpa only [cl24E] using hElt
  have hcross := cl24_cross_NE hj hd hN hE
  simp only [lieSylowExponent, cl24E] at hcross
  by_cases hn'ev : Even n'
  · rw [if_pos hn'ev] at hcross
    have h4 := cl24_PSU_rel_even (by omega : 1 < n') hcross
    have hrel : 2 * (n - 1) = n' := by
      have hc : (2 * (n - 1)) * (2 * n) = n' * (2 * n) := by nlinarith only [h4]
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n) hc
    rw [if_pos hn'ev, ← hrel] at hEltn
    omega
  · rw [if_neg hn'ev] at hcross
    have h4 := cl24_PSU_rel_odd (by omega : 0 < n') hcross
    have hrel : 2 * (n - 1) = n' - 1 := by
      have hc : (2 * (n - 1)) * (2 * n) = (n' - 1) * (2 * n) := by nlinarith only [h4]
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n) hc
    have hn'val : n' = 2 * (n - 1) + 1 := by omega
    rw [if_neg hn'ev, hn'val] at hEltn
    omega

private theorem cl24_finPSU_PSU {n n' j d : ℕ}
    (hadm : StatedLieAdmissible .PSU n 3 j) (hadm' : StatedLieAdmissible .PSU n' 3 d)
    (hjd : j < d)
    (hN : lieSylowExponent .PSU n * j = lieSylowExponent .PSU n' * d)
    (hE : j * cl24E .PSU n = d * cl24E .PSU n')
    (hX : ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      s * (lieOrderDivisor .PSU n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor .PSU n (3 ^ j) : ℤ)
        ≠ 0 ∧
      (3 : ℤ) ^ (2 * j) ∣
        s * (lieOrderDivisor .PSU n' (3 ^ d) : ℤ) -
          s' * (lieOrderDivisor .PSU n (3 ^ j) : ℤ)) : False := by
  have hDle : lieOrderDivisor .PSU n (3 ^ j) ≤ 3 ^ j + 1 := cl24_D_le hadm
  obtain ⟨-, hj1, hn3, -⟩ := hadm
  obtain ⟨-, hd1, hn'3, -⟩ := hadm'
  have hj : 0 < j := by omega
  have hd : 0 < d := by omega
  have hEpos : 0 < cl24E .PSU n' := cl24_PSU_E_pos n' hn'3
  have hElt := cl24_E_lt hj hjd hE hEpos
  have hEltn : (if Even n' then 2 * (n' - 1) else 2 * n') <
      (if Even n then 2 * (n - 1) else 2 * n) := by
    simpa only [cl24E] using hElt
  have hcross := cl24_cross_NE hj hd hN hE
  simp only [lieSylowExponent, cl24E] at hcross
  by_cases hn'ev : Even n'
  · rw [if_pos hn'ev] at hcross
    by_cases hnev : Even n
    · rw [if_pos hnev] at hcross
      have h4 := cl24_PSU_rel_even (by omega : 1 < n') hcross
      have hrel : n = n' := by
        have ht := cl24_tri n
        have hc : n * (2 * (n - 1)) = n' * (2 * (n - 1)) := by nlinarith only [h4, ht]
        exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * (n - 1)) hc
      rw [if_pos hn'ev, if_pos hnev, hrel] at hEltn
      omega
    · rw [if_neg hnev] at hcross
      have h4 := cl24_PSU_rel_even (by omega : 1 < n') hcross
      have hrel : n - 1 = n' := by
        have ht := cl24_tri n
        have hc : (n - 1) * (2 * n) = n' * (2 * n) := by nlinarith only [h4, ht]
        exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n) hc
      have hnodd : Odd n := Nat.not_even_iff_odd.mp hnev
      have hEn : cl24E .PSU n = 2 * n := by simp only [cl24E, if_neg hnev]
      have hEevenn' : cl24E .PSU n' = 2 * (n' - 1) := by simp only [cl24E, if_pos hn'ev]
      have hE' : j * (2 * n) = d * (2 * (n' - 1)) := by
        have h := hE
        rw [hEn, hEevenn'] at h
        exact h
      have hsub : n' - 1 = n - 2 := by omega
      rw [hsub] at hE'
      have hjn : j * n = d * (n - 2) := by
        have h2 : (j * n) * 2 = (d * (n - 2)) * 2 := by nlinarith only [hE']
        exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) h2
      have hcop : Nat.Coprime (n - 2) n := by
        have h2n : 2 ≤ n := by omega
        exact (Nat.coprime_self_sub_left h2n).2 (Nat.coprime_two_left.mpr hnodd)
      have hdvd : (n - 2) ∣ j * n := by
        rw [hjn]
        exact Nat.dvd_mul_left (n - 2) d
      have hdivj : (n - 2) ∣ j := (hcop.dvd_mul_right).1 hdvd
      have hlej : n - 2 ≤ j := Nat.le_of_dvd (by omega : 0 < j) hdivj
      have hD' : lieOrderDivisor .PSU n' (3 ^ d) ≤ 4 * j := by
        have hdvd' : lieOrderDivisor .PSU n' (3 ^ d) ∣ n' := cl24_D_PSU_dvd n' (3 ^ d)
        have hn'pos : 0 < n' := by omega
        have h1 : lieOrderDivisor .PSU n' (3 ^ d) ≤ n' := Nat.le_of_dvd hn'pos hdvd'
        have h2 : n' ≤ j + 1 := by omega
        have h3 : j + 1 ≤ 4 * j := by omega
        omega
      have hsize := cl24_size_of_digit hX
      have hcontra := cl24_digit_contra4 hj1 hDle hD'
      omega
  · rw [if_neg hn'ev] at hcross
    by_cases hnev : Even n
    · rw [if_pos hnev] at hcross
      have h4 := cl24_PSU_rel_odd (by omega : 0 < n') hcross
      have hrel : n + 1 = n' := by
        have ht := cl24_tri n
        have hc : n * (2 * (n - 1)) = (n' - 1) * (2 * (n - 1)) := by nlinarith only [h4, ht]
        have : n = n' - 1 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * (n - 1)) hc
        omega
      have hn'val : n' = n + 1 := by omega
      rw [if_neg hn'ev, if_pos hnev, hn'val] at hEltn
      omega
    · rw [if_neg hnev] at hcross
      have h4 := cl24_PSU_rel_odd (by omega : 0 < n') hcross
      have hrel : n = n' := by
        have ht := cl24_tri n
        have hc : (n - 1) * (2 * n) = (n' - 1) * (2 * n) := by nlinarith only [h4, ht]
        have : n - 1 = n' - 1 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n) hc
        omega
      rw [if_neg hn'ev, if_neg hnev, hrel] at hEltn
      omega

theorem cl24_finPSU_cla {τ : StatedLieTag} {n n' j d : ℕ}
    (hτ : τ = .PSL ∨ τ = .PSU ∨ τ = .PSp ∨ τ = .POmegaOdd ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus)
    (hadm : StatedLieAdmissible τ n 3 j) (hadm' : StatedLieAdmissible .PSU n' 3 d) (hjd : j < d)
    (hN : lieSylowExponent τ n * j = lieSylowExponent .PSU n' * d)
    (hE : j * cl24E τ n = d * cl24E .PSU n')
    (hX : ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      s * (lieOrderDivisor .PSU n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ) ≠ 0 ∧
      (3 : ℤ) ^ (2 * j) ∣
        s * (lieOrderDivisor .PSU n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ)) :
    False := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cl24_finPSU_PSL hadm hadm' hjd hN hE
  · exact cl24_finPSU_PSU hadm hadm' hjd hN hE hX
  · exact cl24_finPSU_PSp hadm hadm' hjd hN hE
  · exact cl24_finPSU_POmegaOdd hadm hadm' hjd hN hE
  · exact cl24_finPSU_POmegaPlus hadm hadm' hjd hN hE
  · exact cl24_finPSU_POmegaMinus hadm hadm' hjd hN hE

end CFSG.OddStandard.SmallF3.HypA2Leaves
