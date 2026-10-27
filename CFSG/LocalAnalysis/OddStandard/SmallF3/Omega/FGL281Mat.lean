module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {K : Type*} [Field K]

theorem fg_trace_eq_of_twisted (M : Matrix.GeneralLinearGroup (Fin 2) K) (σ : K ≃+* K)
    {B : Matrix (Fin 2) (Fin 2) K}
    (h : (M : Matrix (Fin 2) (Fin 2) K) * B.map σ = B * M) : σ B.trace = B.trace := by
  have h1 : B = (M : Matrix (Fin 2) (Fin 2) K) * B.map σ *
      ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  have h2 : B.trace = (B.map σ).trace := by
    conv_lhs => rw [h1]
    exact Matrix.trace_units_conj M (B.map σ)
  exact (AddMonoidHom.map_trace σ.toAddMonoidHom B).trans h2.symm

theorem fg_pow_twelve_of_trace {B : Matrix (Fin 2) (Fin 2) K} (hdet : B.det = 1)
    (ht : B.trace ^ 3 = B.trace) : B ^ 12 = 1 := by
  have hCH : B * B = B.trace • B - 1 := by
    have : B * B = B.trace • B - B.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
          Matrix.one_apply] <;> ring
    rwa [hdet, one_smul] at this
  have h0 : B.trace = 0 ∨ B.trace = 1 ∨ B.trace = -1 := by
    have h : B.trace * ((B.trace - 1) * (B.trace + 1)) = 0 := by linear_combination ht
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
      · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))
  rcases h0 with h | h | h
  · rw [h, zero_smul, zero_sub] at hCH
    calc B ^ 12 = (B * B) ^ 6 := by rw [← pow_two, ← pow_mul]
      _ = (-1) ^ 6 := by rw [hCH]
      _ = 1 := by norm_num
  · rw [h, one_smul] at hCH
    have h3 : B ^ 3 = -1 := by
      calc B ^ 3 = B * (B * B) := by noncomm_ring
        _ = B * (B - 1) := by rw [hCH]
        _ = B * B - B := by noncomm_ring
        _ = -1 := by rw [hCH]; noncomm_ring
    calc B ^ 12 = (B ^ 3) ^ 4 := by rw [← pow_mul]
      _ = 1 := by rw [h3]; norm_num
  · rw [h, neg_smul, one_smul] at hCH
    have h3 : B ^ 3 = 1 := by
      calc B ^ 3 = B * (B * B) := by noncomm_ring
        _ = B * (-B - 1) := by rw [hCH]
        _ = -(B * B) - B := by noncomm_ring
        _ = 1 := by rw [hCH]; noncomm_ring
    calc B ^ 12 = (B ^ 3) ^ 4 := by rw [← pow_mul]
      _ = 1 := by rw [h3]; simp

end CFSG.OddStandard.SmallF3.Omega
