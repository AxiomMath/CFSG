module

public import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

public section

namespace CFSG.LinearAlgebra.IntegralTwo

open Matrix

theorem det_trace_of_pow_eq_one {N : Matrix (Fin 2) (Fin 2) ℤ} {k : ℕ} (hk : 0 < k)
    (hN : N ^ k = 1) :
    (N.det = 1 ∧ |N.trace| ≤ 2) ∨ (N.det = -1 ∧ N.trace = 0) := by
  have hdet1 : ∀ {P : Matrix (Fin 2) (Fin 2) ℤ}, P ^ k = 1 → P.det = 1 → |P.trace| ≤ 2 := by
    intro P hP hd
    by_contra h
    push Not at h
    have h2 := Matrix.two_lt_abs_trace_pow (R := ℤ) hd (by omega) (n := k) hk.ne'
    rw [hP, Matrix.trace_one, Fintype.card_fin] at h2
    norm_num at h2
  have hu : IsUnit N.det := by
    have : N.det ^ k = 1 := by rw [← Matrix.det_pow, hN, Matrix.det_one]
    exact IsUnit.of_pow_eq_one this hk.ne'
  rcases Int.isUnit_iff.1 hu with hd | hd
  · exact Or.inl ⟨hd, hdet1 hN hd⟩
  · refine Or.inr ⟨hd, ?_⟩
    have hN2 : (N ^ 2) ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hN, one_pow]
    have hd2 : (N ^ 2).det = 1 := by rw [Matrix.det_pow, hd]; norm_num
    have ht2 := hdet1 hN2 hd2
    have htr : (N ^ 2).trace = N.trace ^ 2 + 2 := by
      have := Matrix.trace_pow_add_two_fin_two N 0
      simp only [zero_add, pow_one, pow_zero, Matrix.trace_one, Fintype.card_fin, hd] at this
      rw [this]; push_cast; ring
    rw [htr, abs_of_nonneg (by positivity)] at ht2
    nlinarith [sq_nonneg N.trace]

end CFSG.LinearAlgebra.IntegralTwo
