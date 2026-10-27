module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10U38Mat
public import Mathlib.Tactic.LinearCombination

public section

open Matrix

namespace CFSG.HardMathSupport.Solomon.Coordinator.U38

variable {K : Type*} [Field K]

@[expose] def av (ω : K) : Fin 3 → K := ![1, ω, ω ^ 2]

section Entries

variable (ω : K)

theorem mA_apply (i j : Fin 3) : mA ω i j = if i = j then av ω i else 0 := by
  fin_cases i <;> fin_cases j <;> simp [mA, av]

theorem mul_mA_apply (s : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (s * mA ω) i j = s i j * av ω j := by
  simp [Matrix.mul_apply, mA_apply]

theorem mA_mul_apply (s : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (mA ω * s) i j = av ω i * s i j := by
  simp [Matrix.mul_apply, mA_apply]

end Entries

theorem shift_cube (x y z : K) :
    (!![0, x, 0; 0, 0, y; z, 0, 0] : Matrix (Fin 3) (Fin 3) K) ^ 3 = (x * y * z) • 1 := by
  rw [pow_succ, pow_succ, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> first | ring1 | simp | grind

theorem shift_cube' (x y z : K) :
    (!![0, 0, x; y, 0, 0; 0, z, 0] : Matrix (Fin 3) (Fin 3) K) ^ 3 = (x * y * z) • 1 := by
  rw [pow_succ, pow_succ, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> first | ring1 | simp | grind

section Torus

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0)
include hω h2

theorem av_sub_ne (i j : Fin 3) (hij : i ≠ j) : av ω j - av ω i ≠ 0 := by
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  fin_cases i <;> fin_cases j <;> simp [av] at hij ⊢ <;> grind

theorem av_shift_ne_one (i j : Fin 3) (hij : j ≠ i + 1) : av ω j - ω * av ω i ≠ 0 := by
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  fin_cases i <;> fin_cases j <;> simp [av] at hij ⊢ <;> grind

theorem av_shift_ne_two (i j : Fin 3) (hij : j ≠ i + 2) : av ω j - ω ^ 2 * av ω i ≠ 0 := by
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  fin_cases i <;> fin_cases j <;> simp [av] at hij ⊢ <;> grind


theorem torus_A (bar : K →+* K) (hbar : ∀ x, bar x = x ^ 8)
    {s t : Matrix (Fin 3) (Fin 3) K} (hst : s * t = 1) (hu : (s.map bar)ᵀ * s = 1)
    {l : K} (hl : s * mA ω = l • (mA ω * s)) :
    ∃ c : K, s ^ 9 = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have E : ∀ i j, s i j * (av ω j - l * av ω i) = 0 := by
    intro i j
    have := congrFun (congrFun hl i) j
    rw [mul_mA_apply, Matrix.smul_apply, mA_mul_apply, smul_eq_mul] at this
    linear_combination this
  have hrow : ∃ j, s 0 j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := congrFun (congrFun hst 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hcon] at this
  obtain ⟨j0, hj0⟩ := hrow
  have hl' : l = av ω j0 := by
    have h1 : av ω j0 - l * av ω 0 = 0 := (mul_eq_zero.1 (E 0 j0)).resolve_left hj0
    have h0 : av ω 0 = 1 := by simp [av]
    rw [h0, mul_one] at h1
    exact (sub_eq_zero.1 h1).symm
  have hcube : ∀ x : Matrix (Fin 3) (Fin 3) K, ∀ c : K, x ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) K) →
      ∃ c' : K, x ^ 9 = c' • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro x c hx
    refine ⟨c ^ 3, ?_⟩
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hx, smul_pow, one_pow]
  fin_cases j0
  ·
    have hl1 : l = 1 := by simpa [av] using hl'
    have hoff : ∀ i j, i ≠ j → s i j = 0 := fun i j hij =>
      (mul_eq_zero.1 (E i j)).resolve_right (by
        rw [hl1, one_mul]
        exact av_sub_ne ω hω h2 i j hij)
    have hdiag : s = Matrix.diagonal (fun i => s i i) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
    have hd : ∀ i, bar (s i i) * s i i = 1 := by
      intro i
      have := congrFun (congrFun hu i) i
      simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.one_apply_eq] at this
      fin_cases i <;> simp [hoff] at this ⊢ <;> simpa using this
    refine ⟨1, ?_⟩
    rw [hdiag, Matrix.diagonal_pow, one_smul]
    ext i j
    by_cases hij : i = j
    · subst hij
      have := hd i
      rw [hbar] at this
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.pow_apply]
      rw [← this]
      ring
    · simp [Matrix.diagonal_apply_ne _ hij, hij]
  ·
    have hl1 : l = ω := by simpa [av] using hl'
    have hsupp : ∀ i j, j ≠ i + 1 → s i j = 0 := fun i j hij =>
      (mul_eq_zero.1 (E i j)).resolve_right (by
        rw [hl1]
        exact av_shift_ne_one ω hω h2 i j hij)
    have z00 : s 0 0 = 0 := hsupp 0 0 (by decide)
    have z02 : s 0 2 = 0 := hsupp 0 2 (by decide)
    have z10 : s 1 0 = 0 := hsupp 1 0 (by decide)
    have z11 : s 1 1 = 0 := hsupp 1 1 (by decide)
    have z21 : s 2 1 = 0 := hsupp 2 1 (by decide)
    have z22 : s 2 2 = 0 := hsupp 2 2 (by decide)
    have hs : s = !![0, s 0 1, 0; 0, 0, s 1 2; s 2 0, 0, 0] := by
      rw [Matrix.eta_fin_three s]
      simp [z00, z02, z10, z11, z21, z22]
    refine hcube s (s 0 1 * s 1 2 * s 2 0) ?_
    rw [hs]
    simpa using shift_cube (s 0 1) (s 1 2) (s 2 0)
  ·
    have hl1 : l = ω ^ 2 := by simpa [av] using hl'
    have hsupp : ∀ i j, j ≠ i + 2 → s i j = 0 := fun i j hij =>
      (mul_eq_zero.1 (E i j)).resolve_right (by
        rw [hl1]
        exact av_shift_ne_two ω hω h2 i j hij)
    have z00 : s 0 0 = 0 := hsupp 0 0 (by decide)
    have z01 : s 0 1 = 0 := hsupp 0 1 (by decide)
    have z11 : s 1 1 = 0 := hsupp 1 1 (by decide)
    have z12 : s 1 2 = 0 := hsupp 1 2 (by decide)
    have z20 : s 2 0 = 0 := hsupp 2 0 (by decide)
    have z22 : s 2 2 = 0 := hsupp 2 2 (by decide)
    have hs : s = !![0, 0, s 0 2; s 1 0, 0, 0; 0, s 2 1, 0] := by
      rw [Matrix.eta_fin_three s]
      simp [z00, z01, z11, z12, z20, z22]
    refine hcube s (s 0 2 * s 1 0 * s 2 1) ?_
    rw [hs]
    simpa using shift_cube' (s 0 2) (s 1 0) (s 2 1)

end Torus

end CFSG.HardMathSupport.Solomon.Coordinator.U38
