module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open Matrix

variable {L : Type} [Field L]

theorem exists_perm_conj_diag_two {C C' : Matrix (Fin 2) (Fin 2) L} (h1 : C * C' = 1)
    (h2 : C' * C = 1) {y : L} (hy : y ≠ 0) (hy2 : y ≠ y⁻¹)
    (hd01 : (C * Matrix.diagonal ![y, y⁻¹] * C') 0 1 = 0)
    (hd10 : (C * Matrix.diagonal ![y, y⁻¹] * C') 1 0 = 0) :
    ∃ ρ : Equiv.Perm (Fin 2), ∀ v : Fin 2 → L,
      C * Matrix.diagonal v * C' = Matrix.diagonal (fun k => v (ρ k)) := by
  have hdet : C.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hC' : C' = C.det⁻¹ • C.adjugate := by
    have : C⁻¹ = C' := Matrix.inv_eq_right_inv h1
    rw [← this, Matrix.inv_def, Ring.inverse_eq_inv']
  have ha : ∀ i j, C' i j = C.det⁻¹ * C.adjugate i j := fun i j => by rw [hC']; rfl
  rw [Matrix.adjugate_fin_two] at ha
  have hN01 : (C * Matrix.diagonal ![y, y⁻¹] * C') 0 1 =
      C.det⁻¹ * (C 0 0 * C 0 1) * (y⁻¹ - y) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, ha]
    simp
    ring
  have hN10 : (C * Matrix.diagonal ![y, y⁻¹] * C') 1 0 =
      C.det⁻¹ * (C 1 0 * C 1 1) * (y - y⁻¹) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, ha]
    simp
    ring
  have hyy : y⁻¹ - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy2)
  have hyy' : y - y⁻¹ ≠ 0 := sub_ne_zero.2 hy2
  have hdetinv : C.det⁻¹ ≠ 0 := inv_ne_zero hdet
  have hp1 : C 0 0 * C 0 1 = 0 := by
    rw [hN01] at hd01
    rcases mul_eq_zero.1 hd01 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hdetinv
      · exact h
    · exact absurd h hyy
  have hp2 : C 1 0 * C 1 1 = 0 := by
    rw [hN10] at hd10
    rcases mul_eq_zero.1 hd10 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hdetinv
      · exact h
    · exact absurd h hyy'
  rw [Matrix.det_fin_two] at hdet
  by_cases h00 : C 0 0 = 0
  ·
    have h01 : C 0 1 ≠ 0 := fun h => hdet (by rw [h00, h]; ring)
    have h10 : C 1 0 ≠ 0 := fun h => hdet (by rw [h00, h]; ring)
    have h11 : C 1 1 = 0 := by
      rcases mul_eq_zero.1 hp2 with h | h
      · exact absurd h h10
      · exact h
    refine ⟨Equiv.swap 0 1, fun v => ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, ha, h00, h11,
        Matrix.det_fin_two] <;>
      field_simp <;> ring
  · have h01 : C 0 1 = 0 := by
      rcases mul_eq_zero.1 hp1 with h | h
      · exact absurd h h00
      · exact h
    have h11 : C 1 1 ≠ 0 := fun h => hdet (by rw [h01, h]; ring)
    have h10 : C 1 0 = 0 := by
      rcases mul_eq_zero.1 hp2 with h | h
      · exact h
      · exact absurd h h11
    refine ⟨1, fun v => ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, ha, h01, h10,
        Matrix.det_fin_two] <;>
      field_simp <;> ring

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
