module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G]

theorem _root_.CFSG.CGT.Timmesfeld75.IsTI.subgroupOf {T : Subgroup G} (hTI : IsTI T)
    (H : Subgroup G) : IsTI (T.subgroupOf H) := by
  intro g
  have h := hTI (g : G)
  have hinf : (T.subgroupOf H ⊓ conjSubgroup g (T.subgroupOf H)) =
      (T ⊓ conjSubgroup (g : G) T).subgroupOf H := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, mem_conjSubgroup]
    constructor
    · rintro ⟨hxT, hxconj⟩
      refine ⟨hxT, ?_⟩
      show (x : G) ∈ conjSubgroup (g : G) T
      rw [mem_conjSubgroup]
      rw [Subgroup.mem_subgroupOf] at hxconj
      simpa using hxconj
    · rintro ⟨hxT, hxconj⟩
      refine ⟨hxT, ?_⟩
      change g⁻¹ * x * g ∈ T.subgroupOf H
      have hxconj' : (x : G) ∈ conjSubgroup (g : G) T := hxconj
      rw [mem_conjSubgroup] at hxconj'
      exact hxconj'
  rcases h with hbot | htop
  · left
    rw [hinf, hbot, Subgroup.bot_subgroupOf]
  · right
    rw [hinf, htop]

end CFSG.GroupTheory

end
