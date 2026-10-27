module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.GlaubermanReplacement
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonAmbient

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem subgroupOf_commutator_map {G : Type u} [Group G]
    (subgroup overgroup : Subgroup G) (hle : subgroup ≤ overgroup) :
    (⁅subgroup.subgroupOf overgroup, subgroup.subgroupOf overgroup⁆ : Subgroup overgroup).map overgroup.subtype =
      ⁅subgroup, subgroup⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hle]

theorem subgroupOf_commutator_centralizes {G : Type u} [Group G]
    (subgroup overgroup : Subgroup G) (hle : subgroup ≤ overgroup)
    (hclass : ⁅subgroup, subgroup⁆ ≤ Subgroup.centralizer (subgroup : Set G)) :
    ⁅subgroup.subgroupOf overgroup, subgroup.subgroupOf overgroup⁆ ≤
      Subgroup.centralizer (subgroup.subgroupOf overgroup : Set overgroup) := by
  intro element helement
  have hambient : (element : G) ∈ ⁅subgroup, subgroup⁆ := by
    rw [← subgroupOf_commutator_map subgroup overgroup hle]
    exact Subgroup.mem_map.mpr ⟨element, helement, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (hclass hambient) member hmember

theorem ambient_glauberman_replacement_witness {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime)
    (overgroup normal : Subgroup G) (hpgroup : IsPGroup prime overgroup)
    (hnormalLe : normal ≤ overgroup) (hnormal : (normal.subgroupOf overgroup).Normal)
    (hclass : ⁅normal, normal⁆ ≤ Subgroup.centralizer (normal : Set G))
    (hderived : ⁅normal, normal⁆ ≤ thompsonCenterOf overgroup)
    (hnot : ¬normal ≤ thompsonCenterOf overgroup) :
    ∃ abelian : Subgroup G, abelian ≤ overgroup ∧ MaximumOrderAbelian (abelian.subgroupOf overgroup) ∧
      ¬normal ≤ abelian ∧ normal ≤ Subgroup.normalizer (abelian : Set G) := by
  have hinternalDerived : ⁅normal.subgroupOf overgroup, normal.subgroupOf overgroup⁆ ≤ thompsonOrderCenter overgroup := by
    have hmap : (⁅normal.subgroupOf overgroup, normal.subgroupOf overgroup⁆ : Subgroup overgroup).map overgroup.subtype ≤
        (thompsonOrderCenter overgroup).map overgroup.subtype := by
      rw [subgroupOf_commutator_map normal overgroup hnormalLe]
      exact hderived
    have hbound := Subgroup.map_le_iff_le_comap.mp hmap
    rwa [Subgroup.comap_map_eq_self_of_injective overgroup.subtype_injective] at hbound
  rcases glauberman_replacement prime hprime hodd hpgroup (normal.subgroupOf overgroup) hnormal
      (subgroupOf_commutator_centralizes normal overgroup hnormalLe hclass) hinternalDerived with hall | hwitness
  · have hle : normal.subgroupOf overgroup ≤ thompsonOrderCenter overgroup := by
      rw [thompsonOrderCenter_eq_intersection]
      apply le_iInf
      intro candidate
      exact hall candidate.val candidate.property
    have hmapped := Subgroup.map_mono (f := overgroup.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hnormalLe] at hmapped
    exact False.elim (hnot hmapped)
  · obtain ⟨abelian, hmaximum, hnotContains, hnormalizes⟩ := hwitness
    have hambientLe : abelian.map overgroup.subtype ≤ overgroup := Subgroup.map_subtype_le _
    refine ⟨abelian.map overgroup.subtype, hambientLe, ?_, ?_, ?_⟩
    · change MaximumOrderAbelian ((abelian.map overgroup.subtype).comap overgroup.subtype)
      rwa [Subgroup.comap_map_eq_self_of_injective overgroup.subtype_injective]
    · intro hcontains
      have hbound : normal.subgroupOf overgroup ≤ (abelian.map overgroup.subtype).subgroupOf overgroup :=
        Subgroup.comap_mono hcontains
      change normal.subgroupOf overgroup ≤ (abelian.map overgroup.subtype).comap overgroup.subtype at hbound
      rw [Subgroup.comap_map_eq_self_of_injective overgroup.subtype_injective] at hbound
      exact hnotContains hbound
    · apply Subgroup.le_normalizer_iff.mpr
      intro conjugator hconjugator element helement
      obtain ⟨representative, hrepresentative, rfl⟩ := helement
      have hconjugate := Subgroup.le_normalizer_iff.mp hnormalizes
        (⟨conjugator, hnormalLe hconjugator⟩ : overgroup) hconjugator representative hrepresentative
      exact Subgroup.mem_map.mpr ⟨(⟨conjugator, hnormalLe hconjugator⟩ : overgroup) * representative *
        (⟨conjugator, hnormalLe hconjugator⟩ : overgroup)⁻¹, hconjugate, rfl⟩

end CFSG.RankThreeEvenClassification.Helpers
