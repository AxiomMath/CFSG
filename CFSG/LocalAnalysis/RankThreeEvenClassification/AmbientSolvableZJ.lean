module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableZJFactorization

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem thompsonCenterOf_ne_bot_of_pSubgroup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G)
    (hpgroup : IsPGroup prime subgroup) (hne : subgroup ≠ ⊥) : thompsonCenterOf subgroup ≠ ⊥ := by
  have : Nontrivial subgroup := (Subgroup.nontrivial_iff_ne_bot subgroup).mpr hne
  have hcenterNe := thompsonOrderCenter_ne_bot_of_pGroup subgroup prime hprime hpgroup
  exact fun heq => hcenterNe ((Subgroup.map_eq_bot_iff_of_injective
    (thompsonOrderCenter subgroup) subgroup.subtype_injective).mp heq)

theorem thompsonCenterOf_internal_ambient {G : Type u} [Group G] [Finite G]
    (overgroup : Subgroup G) (subgroup : Subgroup overgroup) :
    (thompsonCenterOf subgroup).map overgroup.subtype =
      thompsonCenterOf (subgroup.map overgroup.subtype) := by
  exact (thompsonCenterOf_map_of_injective_restriction overgroup.subtype subgroup
    (overgroup.subtype_injective.comp subgroup.subtype_injective)).symm

theorem internal_normalizer_ambient_eq {G : Type u} [Group G]
    (overgroup : Subgroup G) (subgroup : Subgroup overgroup) :
    (Subgroup.normalizer (subgroup : Set overgroup)).map overgroup.subtype =
      overgroup ⊓ Subgroup.normalizer (subgroup.map overgroup.subtype : Set G) := by
  have hle : subgroup.map overgroup.subtype ≤ overgroup := Subgroup.map_subtype_le subgroup
  have heq : (subgroup.map overgroup.subtype).subgroupOf overgroup = subgroup := by
    exact Subgroup.comap_map_eq_self_of_injective overgroup.subtype_injective subgroup
  have hnormalizer := Subgroup.subgroupOf_normalizer_eq hle
  rw [heq] at hnormalizer
  rw [← hnormalizer, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem ambient_solvable_zj_normalizer_factorization_sup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hlarge : 5 ≤ prime)
    (overgroup : Subgroup G) [Group.IsSolvable overgroup] (sylow : Sylow prime overgroup) :
    (primeComplementCore overgroup prime).map overgroup.subtype ⊔
      (overgroup ⊓ Subgroup.normalizer
        (thompsonCenterOf ((sylow : Subgroup overgroup).map overgroup.subtype) : Set G)) = overgroup := by
  have hfactor := congrArg (fun subgroup : Subgroup overgroup => subgroup.map overgroup.subtype)
    (solvable_zj_normalizer_factorization_sup prime hprime hlarge sylow)
  rw [Subgroup.map_sup, internal_normalizer_ambient_eq, thompsonCenterOf_internal_ambient] at hfactor
  have htopMap : (⊤ : Subgroup overgroup).map overgroup.subtype = overgroup := by
    ext member
    exact ⟨fun ⟨preimage, _, heq⟩ => heq ▸ preimage.property,
      fun hmember => ⟨⟨member, hmember⟩, Subgroup.mem_top _, rfl⟩⟩
  rwa [htopMap] at hfactor

end CFSG.RankThreeEvenClassification.Helpers
