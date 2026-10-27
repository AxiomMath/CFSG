module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

namespace MF163

open Matrix

variable {K : Type*} [Field K]

theorem mul_self_eq (A : Matrix (Fin 2) (Fin 2) K) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem adjugate_eq (A : Matrix (Fin 2) (Fin 2) K) :
    adjugate A = A.trace • (1 : Matrix (Fin 2) (Fin 2) K) - A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two]

theorem traceless_anticomm {B N : Matrix (Fin 2) (Fin 2) K} (hB : B.trace = 0)
    (hN : N.trace = 0) :
    B * N + N * B = (B * N).trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.trace_fin_two] at hB hN
  have hB' : B 1 1 = -B 0 0 := by linear_combination hB
  have hN' : N 1 1 = -N 0 0 := by linear_combination hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, hB', hN'] <;> ring

theorem pow_four_eq (A : Matrix (Fin 2) (Fin 2) K) :
    A * A * (A * A) = (A.trace ^ 3 - 2 * A.trace * A.det) • A +
      (A.det ^ 2 - A.trace ^ 2 * A.det) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

@[expose] noncomputable def twoTraceless (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  (2 : K) • A - A.trace • (1 : Matrix (Fin 2) (Fin 2) K)

theorem trace_twoTraceless (A : Matrix (Fin 2) (Fin 2) K) : (twoTraceless A).trace = 0 := by
  rw [twoTraceless, Matrix.trace_fin_two]
  simp [Matrix.trace_fin_two]
  ring

theorem det_twoTraceless (A : Matrix (Fin 2) (Fin 2) K) :
    (twoTraceless A).det = 4 * A.det - A.trace ^ 2 := by
  rw [twoTraceless, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [Matrix.trace_fin_two]
  ring

theorem two_mul_self_eq (A : Matrix (Fin 2) (Fin 2) K) :
    (2 : K) • (A * A) = A.trace • twoTraceless A +
      (A.trace ^ 2 - 2 * A.det) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [mul_self_eq, twoTraceless]
  module

section Order4

variable {A : Matrix (Fin 2) (Fin 2) K}

theorem trace_ne_zero (hA2 : ∀ a : K, A * A ≠ a • 1) : A.trace ≠ 0 := by
  intro ht
  apply hA2 (-A.det)
  rw [mul_self_eq, ht, zero_smul, zero_sub, neg_smul]

theorem trace_sq_eq (hA2 : ∀ a : K, A * A ≠ a • 1) (hA4 : ∃ a : K, A * A * (A * A) = a • 1) :
    A.trace ^ 2 = 2 * A.det := by
  obtain ⟨a, ha⟩ := hA4
  have ht := trace_ne_zero hA2
  by_contra hne
  set c₀ := A.trace ^ 3 - 2 * A.trace * A.det with hc₀
  set e := A.det ^ 2 - A.trace ^ 2 * A.det with he
  have hc : c₀ ≠ 0 := by
    intro h
    apply hne
    have h1 : A.trace * (A.trace ^ 2 - 2 * A.det) = 0 := by rw [hc₀] at h; linear_combination h
    rcases mul_eq_zero.1 h1 with h1 | h1
    · exact absurd h1 ht
    · linear_combination h1
  have h0 := pow_four_eq A
  rw [← hc₀, ← he, ha] at h0
  have hsA : A = (c₀⁻¹ * (a - e)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : c₀ • A = (a - e) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [show (a - e) • (1 : Matrix (Fin 2) (Fin 2) K) = a • 1 - e • 1 from sub_smul a e 1, h0]
      abel
    rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
  apply hA2 ((c₀⁻¹ * (a - e)) * (c₀⁻¹ * (a - e)))
  rw [hsA, smul_mul_smul_comm, mul_one]

variable (hA2 : ∀ a : K, A * A ≠ a • 1) (hA4 : ∃ a : K, A * A * (A * A) = a • 1)
include hA2 hA4

theorem det_ne_zero_of_order4 : A.det ≠ 0 := by
  have ht := trace_ne_zero hA2
  have htd := trace_sq_eq hA2 hA4
  intro hd
  rw [hd, mul_zero] at htd
  exact ht (pow_eq_zero_iff (by norm_num) |>.1 htd)

theorem twoTraceless_mul_self :
    twoTraceless A * twoTraceless A = (-(2 * A.det)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hN := mul_self_eq (twoTraceless A)
  rw [trace_twoTraceless, zero_smul, zero_sub, det_twoTraceless, trace_sq_eq hA2 hA4] at hN
  rw [hN, ← neg_smul]
  congr 2
  ring

theorem two_mul_self_eq_smul : (2 : K) • (A * A) = A.trace • twoTraceless A := by
  rw [two_mul_self_eq, trace_sq_eq hA2 hA4, sub_self, zero_smul, add_zero]

theorem mul_self_scalar_of_rel (h2 : (2 : K) ≠ 0) {V : Matrix (Fin 2) (Fin 2) K}
    (hV : V.det ≠ 0) {μ : K} (hrel : A * V * A = μ • V) : ∃ a : K, V * V = a • 1 := by
  have ht := trace_ne_zero hA2
  have hd := det_ne_zero_of_order4 hA2 hA4
  have h1 : A.det • (A * V) + μ • (V * A) = (μ * A.trace) • V := by
    have h := congrArg (· * adjugate A) hrel
    have hl : A * V * A * adjugate A = A.det • (A * V) := by
      rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
    have hr : (μ • V) * adjugate A = μ • (A.trace • V - V * A) := by
      rw [Matrix.smul_mul, adjugate_eq, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    simp only [hl, hr] at h
    rw [h]
    module
  have h1' : A.det • (V * A) + μ • (A * V) = (μ * A.trace) • V := by
    have h := congrArg (adjugate A * ·) hrel
    have hl : adjugate A * (A * V * A) = A.det • (V * A) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_mul]
    have hr : adjugate A * (μ • V) = μ • (A.trace • V - A * V) := by
      rw [Matrix.mul_smul, adjugate_eq, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    simp only [hl, hr] at h
    rw [h]
    module
  have hμ : μ = A.det := by
    have hdet := congrArg Matrix.det hrel
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin] at hdet
    have hsq : (μ - A.det) * (μ + A.det) * V.det = 0 := by linear_combination -hdet
    rcases mul_eq_zero.1 hsq with h | h
    · rcases mul_eq_zero.1 h with h | h
      · linear_combination h
      · exfalso
        have hμ' : μ = -A.det := by linear_combination h
        have hsum : ((2 : K) * A.det * A.trace) • V = 0 := by
          rw [hμ'] at h1 h1'
          have h3 := congrArg₂ (· + ·) h1 h1'
          rw [← sub_eq_zero] at h3
          rw [← h3]
          module
        have hc : (2 : K) * A.det * A.trace ≠ 0 := mul_ne_zero (mul_ne_zero h2 hd) ht
        apply hV
        rw [(smul_eq_zero.1 hsum).resolve_left hc, Matrix.det_zero]
    · exact absurd h hV
  subst hμ
  set N := twoTraceless A with hNdef
  have hAV : A * V + V * A = A.trace • V := by
    have h3 : A.det • (A * V + V * A) = A.det • (A.trace • V) := by
      rw [smul_add, h1, smul_smul, mul_comm]
    exact smul_right_injective _ hd h3
  have hVN : V * N + N * V = 0 := by
    rw [hNdef, twoTraceless, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have h3 : (2 : K) • (V * A) + (2 : K) • (A * V) = (2 : K) • (A.trace • V) := by
      rw [← smul_add, add_comm, hAV]
    rw [← sub_eq_zero] at h3
    rw [← h3]
    module
  have hNN := twoTraceless_mul_self hA2 hA4
  have htrV : V.trace = 0 := by
    have hNVN : N * V * N = (2 * A.det) • V := by
      have hVN' : V * N = -(N * V) := eq_neg_of_add_eq_zero_left hVN
      rw [Matrix.mul_assoc, hVN', Matrix.mul_neg, ← Matrix.mul_assoc, hNN, Matrix.smul_mul,
        Matrix.one_mul, neg_smul, neg_neg]
    have hcyc := Matrix.trace_mul_cycle N V N
    rw [hNVN, hNN, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul] at hcyc
    have h4 : (2 * (2 * A.det)) * V.trace = 0 := by linear_combination hcyc
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h (mul_ne_zero h2 (mul_ne_zero h2 hd))
    · exact h
  refine ⟨-V.det, ?_⟩
  rw [mul_self_eq, htrV, zero_smul, zero_sub, neg_smul]

end Order4

end MF163

end CFSG.ClassicalInvolution.Q3.TL4
