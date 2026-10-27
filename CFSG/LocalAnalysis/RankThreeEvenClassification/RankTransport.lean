module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem isElemAbelian_map {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] (prime : ℕ) (homomorphism : G →* otherGroup)
    (elementary : Subgroup G) (hab : IsElemAbelian prime elementary) :
    IsElemAbelian prime (elementary.map homomorphism) := CFSG.Open.IsElemAbelian.map hab _

theorem pRank_le_map_of_injective {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* otherGroup)
    (hinjective : Function.Injective homomorphism) (subgroup : Subgroup G) :
    pRank prime subgroup ≤ pRank prime (subgroup.map homomorphism) := by
  obtain ⟨elementary, hle, hab, hcard⟩ := pRank_attained prime hprime subgroup
  apply le_csSup (pRank_bddAbove prime hprime (subgroup.map homomorphism))
  refine ⟨elementary.map homomorphism, Subgroup.map_mono hle,
    isElemAbelian_map prime homomorphism elementary hab, ?_⟩
  exact (Subgroup.card_map_of_injective hinjective).trans hcard

theorem pRank_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (equivalence : G ≃* otherGroup)
    (subgroup : Subgroup G) :
    pRank prime (subgroup.map equivalence.toMonoidHom) = pRank prime subgroup := by
  apply le_antisymm
  · have hle := pRank_le_map_of_injective prime hprime equivalence.symm.toMonoidHom
      equivalence.symm.injective (subgroup.map equivalence.toMonoidHom)
    have hcomposition : equivalence.symm.toMonoidHom.comp equivalence.toMonoidHom =
        MonoidHom.id G := by
      ext element
      exact equivalence.symm_apply_apply element
    simpa only [Subgroup.map_map, hcomposition, Subgroup.map_id] using hle
  · exact pRank_le_map_of_injective prime hprime equivalence.toMonoidHom
      equivalence.injective subgroup

theorem pRank_subgroupOf {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (smaller larger : Subgroup G)
    (hle : smaller ≤ larger) : pRank prime (smaller.subgroupOf larger) = pRank prime smaller := by
  apply le_antisymm
  · have hmap := pRank_le_map_of_injective prime hprime larger.subtype
      larger.subtype_injective (smaller.subgroupOf larger)
    simpa only [Subgroup.map_subgroupOf_eq_of_le hle] using hmap
  · obtain ⟨elementary, helementary, hab, hcard⟩ := pRank_attained prime hprime smaller
    have hrestriction := helementary.trans hle
    apply le_csSup (pRank_bddAbove prime hprime (smaller.subgroupOf larger))
    refine ⟨elementary.subgroupOf larger, ?_, ?_, ?_⟩
    · intro element hmem
      exact helementary hmem
    · constructor
      · refine ⟨⟨?_⟩⟩
        intro first second
        apply Subtype.ext
        apply Subtype.ext
        change ((first : larger) : G) * ((second : larger) : G) =
          ((second : larger) : G) * ((first : larger) : G)
        exact congrArg (fun element : elementary => (element : G))
          (isMulCommutative_iff.mp hab.1 (⟨(first : larger), first.property⟩ : elementary)
            (⟨(second : larger), second.property⟩ : elementary))
      · intro element hmem
        apply Subtype.ext
        exact hab.2 element hmem
    · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hrestriction).toEquiv).trans hcard

theorem pRank_top_subgroup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) :
    pRank prime (⊤ : Subgroup subgroup) = pRank prime subgroup := by
  have hrestriction := pRank_subgroupOf prime hprime subgroup subgroup le_rfl
  simpa only [Subgroup.subgroupOf_self] using hrestriction

theorem pRank_eq_of_subgroup_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G)
    (otherSubgroup : Subgroup otherGroup) (equivalence : subgroup ≃* otherSubgroup) :
    pRank prime subgroup = pRank prime otherSubgroup := by
  have hmap := pRank_map_equiv prime hprime equivalence (⊤ : Subgroup subgroup)
  simpa only [Subgroup.map_top_of_surjective equivalence.toMonoidHom equivalence.surjective,
    pRank_top_subgroup prime hprime] using hmap.symm

theorem pRank_eq_sylow {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime G) :
    pRank prime (sylow : Subgroup G) = pRank prime (⊤ : Subgroup G) := by
  have : Fact prime.Prime := ⟨hprime⟩
  apply le_antisymm (pRank_mono prime hprime le_top)
  obtain ⟨elementary, _, hab, hcard⟩ := pRank_attained prime hprime (⊤ : Subgroup G)
  obtain ⟨otherSylow, hle⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  have hrank : pRank prime (⊤ : Subgroup G) ≤ pRank prime (otherSylow : Subgroup G) := by
    apply le_csSup (pRank_bddAbove prime hprime (otherSylow : Subgroup G))
    exact ⟨elementary, hle, hab, hcard⟩
  exact hrank.trans (le_of_eq (pRank_eq_of_subgroup_equiv prime hprime
    (otherSylow : Subgroup G) (sylow : Subgroup G) (otherSylow.equiv sylow)))

theorem pRank_le_sylow {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime G)
    (subgroup : Subgroup G) : pRank prime subgroup ≤ pRank prime (sylow : Subgroup G) := by
  rw [pRank_eq_sylow prime hprime sylow]
  exact pRank_mono prime hprime le_top

end CFSG.RankThreeEvenClassification.Helpers
