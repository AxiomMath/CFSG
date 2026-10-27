module

public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Co

open Subgroup

theorem normal_of_orders {M : Type*} [Group M] {H₁ H₀ : Subgroup M} (hle : H₁ ≤ H₀)
    (h1 : Nat.card H₁ = 360) (h0 : Nat.card H₀ = 720) :
    ∀ h ∈ H₀, ∀ a ∈ H₁, h * a * h⁻¹ ∈ H₁ := by
  have hrel : H₁.relIndex H₀ = 2 := by
    have h := Subgroup.relIndex_mul_card (H := H₁) (K := H₀)
    rw [inf_of_le_left hle, h1, h0] at h
    omega
  haveI : (H₁.subgroupOf H₀).Normal := Subgroup.normal_of_index_eq_two hrel
  intro h hh a ha
  exact Subgroup.mem_subgroupOf.mp
    (Subgroup.Normal.conj_mem inferInstance ⟨a, hle ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨h, hh⟩)

end T84Co

end CFSG.OddStandard.SmallF3.Omega
