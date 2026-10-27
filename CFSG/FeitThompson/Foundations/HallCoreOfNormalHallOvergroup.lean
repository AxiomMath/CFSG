module

public import CFSG.FeitThompson.Local.HallCoreLargestNilpotentNormalHall

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {X : Type*} [Group X]

theorem map_subtype_hallCore_le_hallCore [Finite X] {N : Subgroup X} (hN : N.Normal)
    (hcop : Nat.Coprime (Nat.card N) N.index) :
    (hallCore N).map N.subtype ≤ hallCore X := by
  have := hN
  refine le_hallCore_of_normal_of_isNilpotent_of_coprime ?_ ?_ ?_
  · exact ConjAct.normal_of_characteristic_of_normal
  · exact Group.nilpotent_of_mulEquiv ((hallCore N).equivMapOfInjective _ N.subtype_injective)
  · rw [Subgroup.card_map_of_injective N.subtype_injective, Subgroup.index_map_subtype]
    exact Nat.Coprime.mul_right coprime_natCard_index_hallCore
      (Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card (hallCore N)) hcop)

theorem hallCore_le_map_subtype_hallCore [Finite X] {N : Subgroup X} (hle : hallCore X ≤ N) :
    hallCore X ≤ (hallCore N).map N.subtype := by
  have hsub : (hallCore X).subgroupOf N ≤ hallCore N := by
    refine le_hallCore_of_normal_of_isNilpotent_of_coprime Subgroup.normal_subgroupOf ?_ ?_
    · exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      exact Nat.Coprime.coprime_dvd_right
        ⟨N.index, (Subgroup.relIndex_mul_index hle).symm⟩ coprime_natCard_index_hallCore
  have h := Subgroup.map_mono (f := N.subtype) hsub
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle] at h

theorem map_subtype_hallCore_eq_hallCore [Finite X] {N : Subgroup X} (hN : N.Normal)
    (hcop : Nat.Coprime (Nat.card N) N.index) (hle : hallCore X ≤ N) :
    (hallCore N).map N.subtype = hallCore X :=
  le_antisymm (map_subtype_hallCore_le_hallCore hN hcop) (hallCore_le_map_subtype_hallCore hle)

theorem hallCore_eq_subgroupOf_hallCore [Finite X] {N : Subgroup X} (hN : N.Normal)
    (hcop : Nat.Coprime (Nat.card N) N.index) (hle : hallCore X ≤ N) :
    hallCore N = (hallCore X).subgroupOf N := by
  rw [← map_subtype_hallCore_eq_hallCore hN hcop hle, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective]

theorem natCard_hallCore_eq [Finite X] {N : Subgroup X} (hN : N.Normal)
    (hcop : Nat.Coprime (Nat.card N) N.index) (hle : hallCore X ≤ N) :
    Nat.card (hallCore N) = Nat.card (hallCore X) := by
  rw [← map_subtype_hallCore_eq_hallCore hN hcop hle,
    Subgroup.card_map_of_injective N.subtype_injective]

end CFSG.FeitThompson
