module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Trace

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Ord

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def cheb (τ : F) : ℕ → F
  | 0 => 0
  | 1 => 1
  | (n + 2) => τ * cheb τ (n + 1) - cheb τ n

@[expose] def ordPoly (τ : F) : F := (τ ^ 2 - 4) * τ * (τ ^ 2 - 1) * (τ ^ 4 - 3 * τ ^ 2 + 1)

theorem sq_eq (M : Matrix (Fin 2) (Fin 2) F) (hdet : M.det = 1) :
    M * M = M.trace • M - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination (-1 : F) * hdet

theorem pow_eq (M : Matrix (Fin 2) (Fin 2) F) (hM : M * M = M.trace • M - 1) (n : ℕ) :
    M ^ (n + 1) = cheb M.trace (n + 1) • M -
      cheb M.trace n • (1 : Matrix (Fin 2) (Fin 2) F) := by
  induction n with
  | zero => simp [cheb]
  | succ n ih =>
    rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hM]
    have h2 : cheb M.trace (n + 1 + 1) = M.trace * cheb M.trace (n + 1) - cheb M.trace n := rfl
    rw [h2]
    module

theorem ordPoly_eq_zero_of_scalar {M : Matrix (Fin 2) (Fin 2) F} (hdet : M.det = 1) {c : F}
    (hc : M = c • 1) : ordPoly M.trace = 0 := by
  have hc2 : c * c = 1 := by
    rw [hc, Matrix.det_smul, Matrix.det_one] at hdet
    simpa [pow_two] using hdet
  have htr : M.trace = 2 * c := by
    rw [hc]
    simp
    ring
  rw [htr, ordPoly]
  have h4 : (2 * c) ^ 2 - 4 = 0 := by linear_combination 4 * hc2
  rw [h4]
  ring

theorem cheb_eq_zero_of_pow_scalar {M : Matrix (Fin 2) (Fin 2) F} (hdet : M.det = 1)
    (hsc : ∀ c : F, M ≠ c • 1) {n : ℕ} {s : F} (hs : M ^ (n + 1) = s • 1) :
    cheb M.trace (n + 1) = 0 := by
  have h := pow_eq M (sq_eq M hdet) n
  rw [hs] at h
  by_contra hne
  have h1 : cheb M.trace (n + 1) • M = (s + cheb M.trace n) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [add_smul]
    exact (eq_sub_iff_add_eq.mp h).symm
  refine hsc ((cheb M.trace (n + 1))⁻¹ * (s + cheb M.trace n)) ?_
  calc M = (cheb M.trace (n + 1))⁻¹ • (cheb M.trace (n + 1) • M) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = _ := by rw [h1, smul_smul]

theorem ordPoly_of_pow_scalar {M : Matrix (Fin 2) (Fin 2) F} (hdet : M.det = 1) {k : ℕ}
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5) {s : F} (hs : M ^ k = s • 1) :
    ordPoly M.trace = 0 := by
  by_cases hsc : ∃ c : F, M = c • 1
  · obtain ⟨c, hc⟩ := hsc
    exact ordPoly_eq_zero_of_scalar hdet hc
  · push Not at hsc
    rcases hk with rfl | rfl | rfl | rfl
    · have h := cheb_eq_zero_of_pow_scalar hdet hsc (n := 0) hs
      simp [cheb] at h
    · have h := cheb_eq_zero_of_pow_scalar hdet hsc (n := 1) hs
      simp [cheb] at h
      rw [ordPoly, h]
      ring
    · have h := cheb_eq_zero_of_pow_scalar hdet hsc (n := 2) hs
      have h3 : M.trace ^ 2 - 1 = 0 := by
        simp [cheb] at h
        linear_combination h
      rw [ordPoly, h3]
      ring
    · have h := cheb_eq_zero_of_pow_scalar hdet hsc (n := 4) hs
      have h5 : M.trace ^ 4 - 3 * M.trace ^ 2 + 1 = 0 := by
        simp [cheb] at h
        linear_combination h
      rw [ordPoly, h5]
      ring

theorem ordPoly_of_psl_pow {M : Matrix.SpecialLinearGroup (Fin 2) F} {k : ℕ}
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5)
    (h : (QuotientGroup.mk M : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ^ k = 1) :
    ordPoly (M : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
  have h1 : M ^ k ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
  refine ordPoly_of_pow_scalar M.2 hk (s := r) ?_
  rw [← Matrix.SpecialLinearGroup.coe_pow, ← hr]
  simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

@[expose] def cycQ (M : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) : F :=
  M 1 0 * v 0 ^ 2 + (M 1 1 - M 0 0) * v 0 * v 1 - M 0 1 * v 1 ^ 2

@[expose] def gMat (s : F) (v : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F :=
  !![1 - s * (v 0 * v 1), s * v 0 ^ 2; -(s * v 1 ^ 2), 1 + s * (v 0 * v 1)]

theorem det_gMat (s : F) (v : Fin 2 → F) : (gMat s v).det = 1 := by
  rw [gMat, Matrix.det_fin_two_of]
  ring

@[expose] def gSL (s : F) (v : Fin 2 → F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨gMat s v, det_gMat s v⟩

theorem gSL_mul (s t : F) (v : Fin 2 → F) : gSL s v * gSL t v = gSL (s + t) v := by
  apply Subtype.ext
  show gMat s v * gMat t v = gMat (s + t) v
  rw [gMat, gMat, gMat, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem gSL_zero (v : Fin 2 → F) : gSL 0 v = 1 := by
  apply Subtype.ext
  show gMat 0 v = 1
  rw [gMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem gSL_inv (s : F) (v : Fin 2 → F) : (gSL s v)⁻¹ = gSL (-s) v :=
  inv_eq_of_mul_eq_one_right (by rw [gSL_mul, add_neg_cancel, gSL_zero])

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Ord
