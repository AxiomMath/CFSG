module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Span.Defs

public section

namespace CFSG.LinearAlgebra

theorem preserves_complements_of_normalizes_scalar_block
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {U W : Submodule K V} (hc : IsCompl U W) {T : Subgroup (V ≃ₗ[K] V)}
    (hmove : ∀ t ∈ T, ∀ v : V, t v - v ∈ U)
    (hfix : ∀ t ∈ T, ∀ w ∈ W, t w = w)
    {z : V ≃ₗ[K] V} (hz : z ∈ T) {a : K} (ha : a ≠ 1)
    (hzU : ∀ u ∈ U, z u = a • u) (hzW : ∀ w ∈ W, z w = w)
    {g : V ≃ₗ[K] V} (hg : g ∈ Subgroup.normalizer (T : Set (V ≃ₗ[K] V))) :
    (∀ u ∈ U, g u ∈ U) ∧ (∀ w ∈ W, g w ∈ W) := by
  have ha0 : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have fixed_mem : ∀ v : V, z v = v → v ∈ W := by
    intro v hv
    have hvUW : v ∈ U ⊔ W := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hvUW
    have heq : a • u = u := by
      rw [map_add, hzU u hu, hzW w hw] at hv
      exact add_right_cancel hv
    have hzero : (a - 1) • u = 0 := by simp [sub_smul, heq]
    have hu0 : u = 0 := by
      have h := congrArg (fun v : V => (a - 1)⁻¹ • v) hzero
      simpa [smul_smul, ha0] using h
    simpa [hu0] using hw
  constructor
  · intro u hu
    have hzt : g * z * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hg z).mp hz
    have hm := hmove (g * z * g⁻¹) hzt (g u)
    have hs : (a - 1) • g u ∈ U := by
      simpa [LinearEquiv.mul_apply, hzU u hu, sub_smul] using hm
    have := U.smul_mem (a - 1)⁻¹ hs
    simpa [smul_smul, ha0] using this
  · intro w hw
    have hzt : g⁻¹ * z * g ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hg) z).mp hz
    have hf := hfix (g⁻¹ * z * g) hzt w hw
    have heq : z (g w) = g w := by
      have h := congrArg g hf
      simpa [LinearEquiv.mul_apply] using h
    exact fixed_mem (g w) heq

end CFSG.LinearAlgebra

end
