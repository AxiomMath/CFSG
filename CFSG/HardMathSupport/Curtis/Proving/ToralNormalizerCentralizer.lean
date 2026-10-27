module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Curtis.Proving

variable {Y : Type*} [Group Y]

theorem conj_mem_centralizer_of_mem_normalizer {L : Subgroup Y} {c x : Y}
    (hc : c ∈ Subgroup.normalizer (L : Set Y))
    (hx : x ∈ Subgroup.centralizer (L : Set Y)) :
    c * x * c⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro h hh
  have hL : c⁻¹ * h * c ∈ (L : Set Y) := by
    rw [Subgroup.mem_set_normalizer_iff] at hc
    have := (hc (c⁻¹ * h * c)).mpr (by simpa [mul_assoc] using hh)
    simpa [mul_assoc] using this
  have hxh : (c⁻¹ * h * c) * x = x * (c⁻¹ * h * c) := hx _ hL
  calc h * (c * x * c⁻¹) = c * ((c⁻¹ * h * c) * x) * c⁻¹ := by group
    _ = c * (x * (c⁻¹ * h * c)) * c⁻¹ := by rw [hxh]
    _ = c * x * c⁻¹ * h := by group

end CFSG.HardMathSupport.Curtis.Proving

end
