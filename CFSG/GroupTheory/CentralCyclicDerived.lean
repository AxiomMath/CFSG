module

import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem derived_sup_of_central_factor (E I : Subgroup G)
    (hcentral : ∀ e ∈ E, ∀ i ∈ I, Commute e i)
    (habelian : ∀ i ∈ I, ∀ j ∈ I, Commute i j)
    (hproduct : ∀ x ∈ E ⊔ I, ∃ e ∈ E, ∃ i ∈ I, e * i = x) :
    ⁅E ⊔ I, E ⊔ I⁆ = ⁅E, E⁆ := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨e, he, i, hi, rfl⟩ := hproduct x hx
    obtain ⟨f, hf, j, hj, rfl⟩ := hproduct y hy
    have heJ := hcentral e he j hj
    have hfI := hcentral f hf i hi
    have hiJ := habelian i hi j hj
    have hcomm : ⁅e * i, f * j⁆ = ⁅e, f⁆ := by
      simp only [commutatorElement_def, mul_inv_rev]
      calc
        e * i * (f * j) * (i⁻¹ * e⁻¹) * (j⁻¹ * f⁻¹) =
            e * (i * f) * j * i⁻¹ * e⁻¹ * j⁻¹ * f⁻¹ := by group
        _ = e * (f * i) * j * i⁻¹ * e⁻¹ * j⁻¹ * f⁻¹ := by rw [← hfI.eq]
        _ = e * f * (i * j * i⁻¹) * e⁻¹ * j⁻¹ * f⁻¹ := by group
        _ = e * f * j * e⁻¹ * j⁻¹ * f⁻¹ := by
          have h : i * j * i⁻¹ = j := by rw [hiJ.eq]; group
          rw [h]
        _ = e * f * (j * e⁻¹) * j⁻¹ * f⁻¹ := by group
        _ = e * f * (e⁻¹ * j) * j⁻¹ * f⁻¹ := by rw [← heJ.inv_left.eq]
        _ = e * f * e⁻¹ * f⁻¹ := by group
    rw [hcomm]
    exact Subgroup.commutator_mem_commutator he hf
  · exact Subgroup.commutator_mono le_sup_left le_sup_left

end CFSG
