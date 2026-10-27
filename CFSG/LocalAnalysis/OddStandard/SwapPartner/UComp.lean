module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

theorem eq_or_commute_of_normal_quasisimple {G : Type*} [Group G] [Finite G]
    {Y N₁ N₂ : Subgroup G} (h₁ : N₁ ≤ Y) (h₂ : N₂ ≤ Y) (n₁ : (N₁.subgroupOf Y).Normal)
    (n₂ : (N₂.subgroupOf Y).Normal) (q₁ : CFSG.IsQuasisimple ↥N₁)
    (q₂ : CFSG.IsQuasisimple ↥N₂) : N₁ = N₂ ∨ ⁅N₁, N₂⁆ = ⊥ := by
  have hc₁ : CFSG.IsComponent (N₁.subgroupOf Y) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h₁).symm q₁,
      n₁.isSubnormal⟩
  have hc₂ : CFSG.IsComponent (N₂.subgroupOf Y) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h₂).symm q₂,
      n₂.isSubnormal⟩
  rcases CFSG.LocalCores.distinct_components_commute hc₁ hc₂ with heq | hcomm
  · left
    have h := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr h₁, inf_eq_left.mpr h₂] at h
  · right
    have h := congrArg (Subgroup.map Y.subtype) hcomm
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, Subgroup.map_bot] at h
    rwa [inf_eq_left.mpr h₁, inf_eq_left.mpr h₂] at h

end CFSG.OddStandard.AltStdSec.SwapPartner
