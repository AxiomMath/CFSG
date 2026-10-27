module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDiv

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

private theorem cl24_psu_odd_det {N E n' : ℕ} (hn' : 0 < n')
    (h : N * (2 * n') = (n' * (n' - 1) / 2) * E) : 4 * N = (n' - 1) * E := by
  have h2 : 2 * (N * (2 * n')) = n' * (n' - 1) * E := by
    rw [h, ← mul_assoc, cl24_tri]
  have hEq : n' * (4 * N) = n' * ((n' - 1) * E) := by
    calc n' * (4 * N) = 2 * (N * (2 * n')) := by ring
      _ = n' * (n' - 1) * E := h2
      _ = n' * ((n' - 1) * E) := by rw [mul_assoc]
  exact Nat.eq_of_mul_eq_mul_left hn' hEq

private theorem cl24_psu_even_det {N E n' : ℕ} (hn' : 2 ≤ n')
    (h : N * (2 * (n' - 1)) = (n' * (n' - 1) / 2) * E) : 4 * N = n' * E := by
  have h2 : 2 * (N * (2 * (n' - 1))) = n' * (n' - 1) * E := by
    rw [h, ← mul_assoc, cl24_tri]
  have hEq : (n' - 1) * (4 * N) = (n' - 1) * (n' * E) := by
    calc (n' - 1) * (4 * N) = 2 * (N * (2 * (n' - 1))) := by ring
      _ = n' * (n' - 1) * E := h2
      _ = (n' - 1) * (n' * E) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) hEq

private theorem cl24_j_eq_one {j B : ℕ} (hj : 1 ≤ j) (hB : 3 ^ (2 * j) ≤ B) (hB' : B ≤ 80) :
    j = 1 := by
  by_contra h
  have h2 : 2 ≤ j := by omega
  have h4 : 4 ≤ 2 * j := by omega
  have h5 : 3 ^ 4 ≤ 3 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) h4
  norm_num at h5
  omega

private theorem cl24_lin_even {N E n' j d : ℕ} (hdet : 4 * N = n' * E)
    (hE : j * E = d * (2 * (n' - 1))) : j * E * E = d * (2 * (4 * N - E)) := by
  have h1 : (n' - 1) * E = 4 * N - E := by
    rw [Nat.sub_mul, one_mul, hdet]
  calc j * E * E = (j * E) * E := by ring
    _ = (d * (2 * (n' - 1))) * E := by rw [hE]
    _ = d * (2 * ((n' - 1) * E)) := by ring
    _ = d * (2 * (4 * N - E)) := by rw [h1]

private theorem cl24_lin_odd {N E n' j d : ℕ} (hn' : 1 ≤ n') (hdet : 4 * N = (n' - 1) * E)
    (hE : j * E = d * (2 * n')) : j * E * E = d * (2 * (4 * N + E)) := by
  have h1 : n' * E = 4 * N + E := by
    calc n' * E = ((n' - 1) + 1) * E := by rw [Nat.sub_add_cancel hn']
      _ = (n' - 1) * E + E := by rw [Nat.add_mul, Nat.one_mul]
      _ = 4 * N + E := by rw [← hdet]
  calc j * E * E = (j * E) * E := by ring
    _ = (d * (2 * n')) * E := by rw [hE]
    _ = d * (2 * (n' * E)) := by ring
    _ = d * (2 * (4 * N + E)) := by rw [h1]

theorem cl24_finPSU_exc {τ : StatedLieTag} {n n' j d : ℕ}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6 ∨ τ = .trialityD4)
    (hadm : StatedLieAdmissible τ n 3 j) (hadm' : StatedLieAdmissible .PSU n' 3 d) (hjd : j < d)
    (hN : lieSylowExponent τ n * j = lieSylowExponent .PSU n' * d)
    (hE : j * cl24E τ n = d * cl24E .PSU n')
    (hX : ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      s * (lieOrderDivisor .PSU n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ) ≠ 0 ∧
      (3 : ℤ) ^ (2 * j) ∣
        s * (lieOrderDivisor .PSU n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ)) :
    False := by
  obtain ⟨hp, hd1, hnPU⟩ := hadm'
  have hj1 : 1 ≤ j := hadm.2.1
  have hj : 0 < j := by omega
  have hd : 0 < d := by omega
  have hn'3 : 3 ≤ n' := hnPU.1
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [lieSylowExponent, cl24E] at hN hE
    split_ifs at hE with hn'even
    all_goals
      have hNE := cl24_cross_NE hj hd hN hE
      first
        | have hdet := cl24_psu_even_det (by omega) hNE
        | have hdet := cl24_psu_odd_det (by omega) hNE
      have hdigit := cl24_size_of_digit hX
      have hDle := cl24_D_le_four hadm (by decide) (by decide)
      have hD'le := Nat.le_of_dvd (by omega) (cl24_D_PSU_dvd n' (3 ^ d))
      have hbound : 3 ^ (2 * j) ≤ 4 + n' := by omega
      have hjval : j = 1 := cl24_j_eq_one (by omega) hbound (by omega)
      first
        | have hlin := cl24_lin_even hdet hE
        | have hlin := cl24_lin_odd (by omega) hdet hE
      subst j
      norm_num at hlin hdigit hDle hD'le
      omega

end CFSG.OddStandard.SmallF3.HypA2Leaves
