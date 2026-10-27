module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem polarNondegOn_span_pair_of_polar_eq_one [CharP F 2] {a b : V} (h : polar Q a b = 1) :
    PolarNondegOn Q (Submodule.span F {a, b}) := by
  intro x hx hx'
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hx
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have haa : polar Q a a = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hbb : polar Q b b = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hba : polar Q b a = 1 := by rw [polar_comm]; exact h
  have hs := hx' b (Submodule.subset_span (by simp))
  have ht := hx' a (Submodule.subset_span (by simp))
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h, hbb] at hs
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, haa, hba] at ht
  rw [show s = 0 by simpa using hs, show t = 0 by simpa using ht]
  simp

end CFSG.ClassicalGroups.Orthogonal

end
