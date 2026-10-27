module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Solomon.Proving

variable {H : Type} [Group H]

theorem mk_commute_iff_commutator_mem (Z : Subgroup H) [Z.Normal] (g h : H) :
    (QuotientGroup.mk g : H ⧸ Z) * QuotientGroup.mk h
        = QuotientGroup.mk h * QuotientGroup.mk g ↔
      g * h * g⁻¹ * h⁻¹ ∈ Z := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have key : g * h * g⁻¹ * h⁻¹ = (g * h) * ((g * h)⁻¹ * (h * g))⁻¹ * (g * h)⁻¹ := by
    group
  rw [key]
  constructor
  · intro hk
    exact Subgroup.Normal.conj_mem inferInstance _ (Z.inv_mem hk) _
  · intro hy
    have h1 := Subgroup.Normal.conj_mem inferInstance _ hy (g * h)⁻¹
    have e : (g * h)⁻¹ * ((g * h) * ((g * h)⁻¹ * (h * g))⁻¹ * (g * h)⁻¹) * ((g * h)⁻¹)⁻¹
        = ((g * h)⁻¹ * (h * g))⁻¹ := by
      group
    have h2 := Z.inv_mem h1
    rwa [e, inv_inv] at h2

theorem center_quotient_eq_bot_of_generators (Z : Subgroup H) [Z.Normal] (S : Set H)
    (hZ : ∀ g : H, (∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ Z) → g ∈ Z) :
    Subgroup.center (H ⧸ Z) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hc : ∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ Z := by
    intro s _
    exact (mk_commute_iff_commutator_mem Z g s).1
      (Subgroup.mem_center_iff.1 hx (QuotientGroup.mk s)).symm
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact hZ g hc

end CFSG.HardMathSupport.Solomon.Proving
