module

public import Mathlib.GroupTheory.Commutator.Basic

import Mathlib.Tactic.Group

public section

open scoped commutatorElement

namespace CFSG.GroupTheory

theorem commutator_eq_self_of_mul_mem {G : Type*} [Group G] {X : Subgroup G} {D : Set G}
    (hgen : Subgroup.closure D = X)
    (hclass : ∀ d ∈ D, ∀ e ∈ D, ∃ x ∈ X, e = x * d * x⁻¹)
    {u v : G} (hu : u ∈ D) (hv : v ∈ D) (huv : u * v ∈ D) :
    ⁅X, X⁆ = X := by
  have huX : u ∈ X := hgen ▸ Subgroup.subset_closure hu
  have hvu : v * u⁻¹ ∈ ⁅X, X⁆ := by
    obtain ⟨x, hxX, hxv⟩ := hclass u hu v hv
    have hcomm : ⁅x, u⁆ ∈ ⁅X, X⁆ := Subgroup.commutator_mem_commutator hxX huX
    simpa [hxv, commutatorElement_def] using hcomm
  have hv'u : (u * v) * u⁻¹ ∈ ⁅X, X⁆ := by
    obtain ⟨x, hxX, hxu⟩ := hclass u hu (u * v) huv
    have hcomm : ⁅x, u⁆ ∈ ⁅X, X⁆ := Subgroup.commutator_mem_commutator hxX huX
    simpa [hxu, commutatorElement_def] using hcomm
  have huK : u ∈ ⁅X, X⁆ := by
    have h : (u * v) * u⁻¹ * (v * u⁻¹)⁻¹ ∈ ⁅X, X⁆ :=
      (⁅X, X⁆).mul_mem hv'u ((⁅X, X⁆).inv_mem hvu)
    rwa [show (u * v) * u⁻¹ * (v * u⁻¹)⁻¹ = u by group] at h
  have hD : ∀ d ∈ D, d ∈ ⁅X, X⁆ := by
    intro d hd
    obtain ⟨x, hxX, hxd⟩ := hclass u hu d hd
    have hcomm : ⁅x, u⁆ ∈ ⁅X, X⁆ := Subgroup.commutator_mem_commutator hxX huX
    have hdu : d * u⁻¹ ∈ ⁅X, X⁆ := by
      simpa [hxd, commutatorElement_def] using hcomm
    have h : d * u⁻¹ * u ∈ ⁅X, X⁆ := (⁅X, X⁆).mul_mem hdu huK
    rwa [show d * u⁻¹ * u = d by group] at h
  refine le_antisymm (Subgroup.commutator_le_self X) ?_
  calc X = Subgroup.closure D := hgen.symm
    _ ≤ ⁅X, X⁆ := (Subgroup.closure_le (K := ⁅X, X⁆)).mpr hD

end CFSG.GroupTheory
