module

public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ElementarySylowControl

theorem contained_every_sylow {G : Type*} [Group G] [Finite G]
    (ambient elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (hcontained : elementary ≤ ambient) (hcentral : elementary ≤ Subgroup.centralizer (ambient : Set G))
    (sylow : Sylow 2 ambient) : elementary ≤ (sylow : Subgroup ambient).map ambient.subtype := by
  let : (elementary.subgroupOf ambient).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    ((Subgroup.le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _))
  have htwo : IsPGroup 2 (elementary.subgroupOf ambient) :=
    (InvolutionGeneratedSubgroup.two_of_elementary elementary helementary).comap_subtype
  have hlocal := htwo.le_sylow_of_normal sylow
  intro member hmember
  exact Subgroup.mem_map.mpr ⟨⟨member, hcontained hmember⟩, hlocal hmember, rfl⟩

theorem omega {G : Type*} [Group G] [Finite G]
    (ambient elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (hcontained : elementary ≤ ambient) (hcentral : elementary ≤ Subgroup.centralizer (ambient : Set G))
    (rank : ℕ) (hsize : Nat.card elementary = 2 ^ rank)
    (sylow : Sylow 2 ambient)
    (hab : IsMulCommutative ((sylow : Subgroup ambient).map ambient.subtype))
    (hrank : pRank 2 ((sylow : Subgroup ambient).map ambient.subtype) ≤ rank) :
    InvolutionGeneratedSubgroup.omega ((sylow : Subgroup ambient).map ambient.subtype) = elementary := by
  have helementarySylow := contained_every_sylow ambient elementary helementary hcontained hcentral sylow
  have hlower := TwoRankTransport.rank_le ((sylow : Subgroup ambient).map ambient.subtype) elementary
    helementarySylow helementary rank hsize
  have hequal := le_antisymm hrank hlower
  exact InvolutionGeneratedSubgroup.eq_of_elementary_card _ elementary hab helementary helementarySylow
    (by rw [hequal]; exact hsize)

theorem involutions {G : Type*} [Group G] [Finite G]
    (ambient elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (hcontained : elementary ≤ ambient)
    (homega : ∀ sylow : Sylow 2 ambient,
      InvolutionGeneratedSubgroup.omega ((sylow : Subgroup ambient).map ambient.subtype) = elementary)
    (member : G) : member ∈ ambient ∧ orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1 := by
  constructor
  · rintro ⟨hmember, horder⟩
    have htwo : IsPGroup 2 (Subgroup.zpowers member) := IsPGroup.of_card
      (by rw [Nat.card_zpowers, horder]; rfl : Nat.card (Subgroup.zpowers member) = 2 ^ 1)
    obtain ⟨sylow, hle⟩ := (htwo.comap_subtype (K := ambient)).exists_le_sylow
    have hsylow : member ∈ (sylow : Subgroup ambient).map ambient.subtype :=
      Subgroup.mem_map.mpr ⟨⟨member, hmember⟩, hle (Subgroup.mem_zpowers member), rfl⟩
    refine ⟨?_, fun hone => ?_⟩
    · rw [← homega sylow]
      exact Subgroup.subset_closure ⟨hsylow, orderOf_dvd_iff_pow_eq_one.mp (horder ▸ dvd_rfl)⟩
    · rw [hone, orderOf_one] at horder
      omega
  · rintro ⟨hmember, hne⟩
    exact ⟨hcontained hmember, orderOf_eq_prime (helementary.2 member hmember) hne⟩

end CFSG.ComponentClassification.ElementarySylowControl
