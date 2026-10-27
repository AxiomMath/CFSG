module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.ExtraspecialSplit
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG

variable {G : Type} [Group G] [Finite G]

theorem exists_centralizer_eq_prod_subgroup {Q : Subgroup G} (hQ : IsExtraspecialPGroup 2 ↥Q)
    (hcard : 2 ^ 5 ≤ Nat.card Q) {t : G} (htQ : t ∈ Q) (ht : orderOf t = 2)
    (hnc : t ∉ (center Q).map Q.subtype) :
    ∃ E : Subgroup G, E ≤ Q ∧ IsExtraspecialPGroup 2 ↥E ∧ Nat.card Q = 4 * Nat.card E ∧
      (center Q).map Q.subtype ≤ E ∧ (center ↥E).map E.subtype = (center Q).map Q.subtype ∧
      Disjoint E (zpowers t) ∧ centralizer ({t} : Set G) ⊓ Q = E ⊔ zpowers t := by
  have ht' : orderOf (⟨t, htQ⟩ : Q) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hnc' : (⟨t, htQ⟩ : Q) ∉ center Q := fun h => hnc ⟨_, h, rfl⟩
  obtain ⟨E₀, hE, hcardE, hZE, hcenE, hdisj, hcent⟩ :=
    hQ.exists_centralizer_eq_prod hcard ht' hnc'
  refine ⟨E₀.map Q.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (E₀.equivMapOfInjective Q.subtype Q.subtype_injective) hE
  · rw [Subgroup.card_map_of_injective Q.subtype_injective]
    exact hcardE
  · exact Subgroup.map_mono hZE
  · have h1 := RankThree.PartOne.Torsion37.inSubgroup_center_map Q.subtype Q.subtype_injective E₀
    unfold inSubgroup at h1
    rw [h1, hcenE]
  · rw [Subgroup.disjoint_def]
    rintro _ ⟨e, he, rfl⟩ hx
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
    have hek : e = (⟨t, htQ⟩ : Q) ^ k := Subtype.ext hk.symm
    have := Subgroup.disjoint_def.1 hdisj he (hek ▸ zpow_mem (mem_zpowers _) k)
    show (e : G) = 1
    rw [this]; rfl
  · have hz : (zpowers (⟨t, htQ⟩ : Q)).map Q.subtype = zpowers t := MonoidHom.map_zpowers _ _
    apply le_antisymm
    · rintro x ⟨hxc, hxQ⟩
      have hxq : (⟨x, hxQ⟩ : Q) ∈ centralizer ({(⟨t, htQ⟩ : Q)} : Set Q) := by
        rw [mem_centralizer_singleton_iff]
        exact Subtype.ext (mem_centralizer_singleton_iff.1 hxc)
      rw [hcent] at hxq
      rw [← hz, ← Subgroup.map_sup]
      exact ⟨_, hxq, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨e, he, rfl⟩
        have : e ∈ centralizer ({(⟨t, htQ⟩ : Q)} : Set Q) :=
          hcent ▸ (le_sup_left : E₀ ≤ E₀ ⊔ zpowers (⟨t, htQ⟩ : Q)) he
        exact ⟨mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 this)), e.2⟩
      · exact le_inf (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) (zpowers_le.2 htQ)

end CFSG.EvenSporadicStandard.TwoB
