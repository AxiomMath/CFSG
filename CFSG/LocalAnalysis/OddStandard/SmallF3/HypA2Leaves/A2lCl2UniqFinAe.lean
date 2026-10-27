module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDiv

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

private theorem cl24_PSL_sylow_relation {N E n' j d : ℕ} (hn' : 0 < n') (hj : 0 < j)
    (hd : 0 < d) (hN : N * j = (n' * (n' - 1) / 2) * d) (hE : j * E = d * n') :
    2 * N = (n' - 1) * E := by
  have hcross : N * n' = (n' * (n' - 1) / 2) * E := cl24_cross_NE hj hd hN hE
  have h2 : n' * (2 * N) = n' * ((n' - 1) * E) := by
    calc n' * (2 * N) = 2 * (N * n') := by ring
      _ = 2 * ((n' * (n' - 1) / 2) * E) := by rw [hcross]
      _ = (2 * (n' * (n' - 1) / 2)) * E := by ring
      _ = (n' * (n' - 1)) * E := by rw [cl24_tri]
      _ = n' * ((n' - 1) * E) := by ring
  exact Nat.eq_of_mul_eq_mul_left hn' h2

theorem cl24_finPSL_exc {τ : StatedLieTag} {n n' j d : ℕ}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6 ∨ τ = .trialityD4)
    (hadm : StatedLieAdmissible τ n 3 j) (hadm' : StatedLieAdmissible .PSL n' 3 d) (hjd : j < d)
    (hN : lieSylowExponent τ n * j = lieSylowExponent .PSL n' * d)
    (hE : j * cl24E τ n = d * cl24E .PSL n')
    (hX : ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      s * (lieOrderDivisor .PSL n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ) ≠ 0 ∧
      (3 : ℤ) ^ (2 * j) ∣
        s * (lieOrderDivisor .PSL n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ)) :
    False := by
  have hDbound : lieOrderDivisor τ n (3 ^ j) ≤ 4 := by
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [lieOrderDivisor] <;>
      solve
        | norm_num
        | exact le_trans (Nat.gcd_le_left (m := 3) _ (by norm_num)) (by norm_num)
        | exact le_trans (Nat.gcd_le_left (m := 2) _ (by norm_num)) (by norm_num)
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have hf : 1 ≤ j := by
      have hadm2 := hadm
      simp only [StatedLieAdmissible] at hadm2
      exact hadm2.2.1
    have hd1 : 1 ≤ d := by
      have hadm'2 := hadm'
      simp only [StatedLieAdmissible] at hadm'2
      exact hadm'2.2.1
    have hn'2 : 2 ≤ n' := by
      have hadm'2 := hadm'
      simp only [StatedLieAdmissible] at hadm'2
      exact hadm'2.2.2.1
    have hj : 0 < j := by omega
    have hd : 0 < d := by omega
    have hn' : 0 < n' := by omega
    simp only [lieSylowExponent, cl24E] at hN hE
    have hrel := cl24_PSL_sylow_relation hn' hj hd hN hE
    have hD := hDbound
    have hD' : lieOrderDivisor .PSL n' (3 ^ d) ≤ n' :=
      Nat.le_of_dvd hn' (cl24_D_PSL_dvd n' (3 ^ d))
    have hsize := cl24_size_of_digit hX
    have hj1 : j = 1 := by
      by_contra h
      have h2 : 2 ≤ j := by omega
      have h81 : 81 ≤ 3 ^ (2 * j) := by
        have h4 : 4 ≤ 2 * j := by omega
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ 3 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) h4
      omega
    subst j
    norm_num at *
    have hn'le : n' ≤ 9 := by omega
    clear hN hX
    interval_cases n' <;> omega

end CFSG.OddStandard.SmallF3.HypA2Leaves
