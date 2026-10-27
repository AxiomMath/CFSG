module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem lt_inf_normalizer_of_isNilpotent {P S : Subgroup G} [Group.IsNilpotent P]
    (hSP : S < P) : S < P ⊓ Subgroup.normalizer (S : Set G) := by
  have hlt : S.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hSP.ne
    apply le_antisymm hSP.le
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ S.subgroupOf P := h ▸ Subgroup.mem_top _
    exact this
  have h := Group.normalizerCondition_of_isNilpotent (S.subgroupOf P) hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hSP.le] at h
  have h2 := (Subgroup.map_lt_map_iff_of_injective P.subtype_injective).mpr h
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hSP.le,
    inf_comm] at h2

theorem lt_inf_normalizer_of_isPGroup {p : ℕ} [Fact p.Prime] {P S : Subgroup G} [Finite ↥P]
    (hP : IsPGroup p P) (hSP : S < P) : S < P ⊓ Subgroup.normalizer (S : Set G) := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  exact lt_inf_normalizer_of_isNilpotent hSP

end CFSG.GroupTheory
