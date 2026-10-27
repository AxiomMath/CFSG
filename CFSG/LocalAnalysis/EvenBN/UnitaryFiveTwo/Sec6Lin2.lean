module

import all CFSG.Fischer.F4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow

open Matrix CFSG.Fischer
open scoped MatrixGroups

@[expose] def lowerSL (a : F4) : SL(2, F4) :=
  ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

theorem eq_lowerSL_of_entries {A : SL(2, F4)} (h00 : A 0 0 = 1) (h01 : A 0 1 = 0)
    (h11 : A 1 1 = 1) : A = lowerSL (A 1 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerSL, h00, h01, h11]

theorem lin2_exists_cube_root : ∀ a : F4, a ≠ 0 → ∃ t : F4, t ^ 3 = 1 ∧ t * a * a = F4.ω := by
  decide +kernel

theorem lin2_matrix_five : ∀ a c : F4, a * c = F4.ω →
    (!![1, 0; a, 1] * !![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) F4) ^ 5 = 1 ∧
      (!![1, 0; a, 1] * !![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) F4) ≠ 1 := by
  decide +kernel

theorem exists_order_five_pair (a : F4) (ha : a ≠ 0) :
    ∃ g : SL(2, F4), (lowerSL a * (g * lowerSL a * g⁻¹)) ^ 5 = 1 ∧
      lowerSL a * (g * lowerSL a * g⁻¹) ≠ 1 := by
  obtain ⟨t, ht3, hta⟩ := lin2_exists_cube_root a ha
  have hdet : (!![0, t ^ 2; t, 0] : Matrix (Fin 2) (Fin 2) F4).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F4) * ht3 + (-1 : F4) * F4.two_eq_zero
  have hUdet : (!![1, t * a; 0, 1] : Matrix (Fin 2) (Fin 2) F4).det = 1 := by
    rw [Matrix.det_fin_two_of]
    ring
  obtain ⟨g, hg_val⟩ : ∃ g : SL(2, F4), (g : Matrix (Fin 2) (Fin 2) F4) = !![0, t ^ 2; t, 0] :=
    ⟨⟨!![0, t ^ 2; t, 0], hdet⟩, rfl⟩
  obtain ⟨U, hU_val⟩ : ∃ U : SL(2, F4), (U : Matrix (Fin 2) (Fin 2) F4) = !![1, t * a; 0, 1] :=
    ⟨⟨!![1, t * a; 0, 1], hUdet⟩, rfl⟩
  have hL : (lowerSL a : Matrix (Fin 2) (Fin 2) F4) = !![1, 0; a, 1] := rfl
  have hg : g * lowerSL a = U * g := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg_val, hU_val, hL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hconj : g * lowerSL a * g⁻¹ = U := mul_inv_eq_iff_eq_mul.2 hg
  obtain ⟨h5, hne⟩ := lin2_matrix_five a (t * a) (by linear_combination hta)
  refine ⟨g, ?_, ?_⟩
  · rw [hconj]
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one, hL, hU_val]
    exact h5
  · rw [hconj]
    intro h
    apply hne
    have h' := congrArg Subtype.val h
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hL, hU_val] at h'
    exact h'

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow
