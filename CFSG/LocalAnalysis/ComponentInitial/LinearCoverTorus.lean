module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourRoots

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Matrix LinearFlag LinearFieldFour

variable {K : Type*} [Field K]

theorem diagonal_mul_xM (s : Fin 3 → K) (h1 : s 1 ≠ 0) (a : K) :
    diagonal s * xM a = xM (s 0 * (s 1)⁻¹ * a) * diagonal s := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [xM]
  field_simp

theorem diagonal_mul_yM (s : Fin 3 → K) (h2 : s 2 ≠ 0) (b : K) :
    diagonal s * yM b = yM (s 1 * (s 2)⁻¹ * b) * diagonal s := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [yM]
  field_simp

theorem diagonal_mul_wM (s : Fin 3 → K) (h2 : s 2 ≠ 0) (c : K) :
    diagonal s * wM c = wM (s 0 * (s 2)⁻¹ * c) * diagonal s := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [wM]
  field_simp

@[expose] def diagSL (s : Fin 3 → K) (hs : s 0 * s 1 * s 2 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal s, by rw [det_diagonal, Fin.prod_univ_three, hs]⟩

theorem coe_diagSL (s : Fin 3 → K) (hs : s 0 * s 1 * s 2 = 1) :
    (diagSL s hs : Matrix (Fin 3) (Fin 3) K) = diagonal s :=
  rfl

theorem diag_ne_zero {s : Fin 3 → K} (hs : s 0 * s 1 * s 2 = 1) (i : Fin 3) : s i ≠ 0 := by
  intro h
  fin_cases i <;> simp_all

theorem diagSL_mul_xMat (s : Fin 3 → K) (hs : s 0 * s 1 * s 2 = 1) (a : K) :
    diagSL s hs * xMat a = xMat (s 0 * (s 1)⁻¹ * a) * diagSL s hs := by
  apply Subtype.ext
  change diagonal s * xM a = xM _ * diagonal s
  exact diagonal_mul_xM s (diag_ne_zero hs 1) a

theorem diagSL_mul_yMat (s : Fin 3 → K) (hs : s 0 * s 1 * s 2 = 1) (b : K) :
    diagSL s hs * yMat b = yMat (s 1 * (s 2)⁻¹ * b) * diagSL s hs := by
  apply Subtype.ext
  change diagonal s * yM b = yM _ * diagonal s
  exact diagonal_mul_yM s (diag_ne_zero hs 2) b

theorem diagSL_mul_wMat (s : Fin 3 → K) (hs : s 0 * s 1 * s 2 = 1) (c : K) :
    diagSL s hs * wMat c = wMat (s 0 * (s 2)⁻¹ * c) * diagSL s hs := by
  apply Subtype.ext
  change diagonal s * wM c = wM _ * diagonal s
  exact diagonal_mul_wM s (diag_ne_zero hs 2) c

theorem projDiag_conj_xP (s : Fin 3 → K) (hs : s 0 * s 1 * s 2 = 1) (a : K) :
    proj 3 K (diagSL s hs) * xP a * (proj 3 K (diagSL s hs))⁻¹ = xP (s 0 * (s 1)⁻¹ * a) := by
  rw [mul_inv_eq_iff_eq_mul, xP, xP, ← map_mul, ← map_mul, diagSL_mul_xMat]

theorem projDiag_conj_yP (s : Fin 3 → K) (hs : s 0 * s 1 * s 2 = 1) (b : K) :
    proj 3 K (diagSL s hs) * yP b * (proj 3 K (diagSL s hs))⁻¹ = yP (s 1 * (s 2)⁻¹ * b) := by
  rw [mul_inv_eq_iff_eq_mul, yP, yP, ← map_mul, ← map_mul, diagSL_mul_yMat]

theorem projDiag_conj_wP (s : Fin 3 → K) (hs : s 0 * s 1 * s 2 = 1) (c : K) :
    proj 3 K (diagSL s hs) * wP c * (proj 3 K (diagSL s hs))⁻¹ = wP (s 0 * (s 2)⁻¹ * c) := by
  rw [mul_inv_eq_iff_eq_mul, wP, wP, ← map_mul, ← map_mul, diagSL_mul_wMat]

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
