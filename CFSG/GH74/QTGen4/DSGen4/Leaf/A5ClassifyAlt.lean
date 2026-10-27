module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.QuasithinUnique.A5.Delta5

@[expose] def x0 : Alt5 := a0' * b0'

@[expose] def y0 : Alt5 := b0'⁻¹

theorem x0_mul_y0 : x0 * y0 = a0' := by
  simp [x0, y0]

theorem x0_sq : x0 * x0 = 1 := by
  apply Subtype.ext
  show (a0 * b0) * (a0 * b0) = 1
  decide +kernel

theorem x0_ne_one : x0 ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  revert this
  show ¬ (a0 * b0 = 1)
  decide +kernel

theorem y0_cube : y0 ^ 3 = 1 := by
  apply Subtype.ext
  show (b0⁻¹) ^ 3 = 1
  decide +kernel

theorem a0'_pow_five : a0' ^ 5 = 1 := by
  apply Subtype.ext
  show a0 ^ 5 = 1
  decide +kernel

theorem x0_y0_pow_five : (x0 * y0) ^ 5 = 1 := by
  rw [x0_mul_y0]; exact a0'_pow_five

theorem closure_x0_y0 : Subgroup.closure ({x0, y0} : Set Alt5) = ⊤ := by
  rw [eq_top_iff, ← closure_a5]
  rw [Subgroup.closure_le]
  intro z hz
  rcases hz with rfl | rfl
  · have h1 : x0 ∈ Subgroup.closure ({x0, y0} : Set Alt5) := Subgroup.subset_closure (by simp)
    have h2 : y0 ∈ Subgroup.closure ({x0, y0} : Set Alt5) := Subgroup.subset_closure (by simp)
    have := Subgroup.mul_mem _ h1 h2
    rwa [x0_mul_y0] at this
  · have h2 : y0 ∈ Subgroup.closure ({x0, y0} : Set Alt5) := Subgroup.subset_closure (by simp)
    have := Subgroup.inv_mem _ h2
    simpa [y0] using this

end CFSG.GH74.QTGen4.DSGen4
