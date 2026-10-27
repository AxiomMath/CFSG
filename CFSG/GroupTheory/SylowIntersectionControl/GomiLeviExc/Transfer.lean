module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviBorelFactor
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Chev

public section

namespace CFSG.GroupTheory.GomiLeviExc

open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem isGomiChevTwo_of_surjective {G X : Type} [Group G] [Group X] [Finite X] [Nontrivial X]
    (hq : CFSG.IsQuasisimple G) (hZ : Odd (Nat.card (center G)))
    (hC : IsChevTwo (G ⧸ center G)) (φ : G →* X) (hφ : Function.Surjective φ) :
    IsGomiChevTwo X := by
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  obtain ⟨g, hg⟩ := hφ x
  have hφ1 : ∃ g, φ g ≠ 1 := ⟨g, by rw [hg]; exact hx⟩
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hφ1
  have hqX := CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hφ hφ1
  have hZX := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hq hφ hker
  have hoddX : Odd (Nat.card (center X)) := by
    rw [hZX]
    exact hZ.of_dvd_nat (Subgroup.card_map_dvd (center G) φ)
  have e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq hφ hker
  exact IsGomiChevTwo.of_isQuasisimple hqX hoddX
    (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.isChevTwo_of_mulEquiv e hC)

theorem gomiLeviFactor_of_range_eq {G K : Type} [Group G] [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple G) (hZ : Odd (Nat.card (center G)))
    (hC : IsChevTwo (G ⧸ center G)) (φ : G →* K) {A : Subgroup K} (hA : φ.range = A)
    (hne : A ≠ ⊥) : GomiLeviFactor ↥A := by
  have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne
  refine Or.inl (isGomiChevTwo_of_surjective hq hZ hC
    ((MulEquiv.subgroupCongr hA).toMonoidHom.comp φ.rangeRestrict) ?_)
  exact (MulEquiv.subgroupCongr hA).surjective.comp φ.rangeRestrict_surjective

theorem gomiLeviFactor_of_injective {G K : Type} [Group G] [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple G) (hZ : Odd (Nat.card (center G)))
    (hC : IsChevTwo (G ⧸ center G)) (φ : G →* K) (hφ : Function.Injective φ) {A : Subgroup K}
    (hA : φ.range = A) : GomiLeviFactor ↥A := by
  refine gomiLeviFactor_of_range_eq hq hZ hC φ hA ?_
  have : Nontrivial (G ⧸ center G) := hq.2.1.toNontrivial
  have : Nontrivial G := (QuotientGroup.mk_surjective (s := center G)).nontrivial
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  intro hbot
  have hmem : φ g ∈ A := by
    rw [← hA]
    exact ⟨g, rfl⟩
  rw [hbot, Subgroup.mem_bot, ← map_one φ] at hmem
  exact hg (hφ hmem)

end CFSG.GroupTheory.GomiLeviExc
