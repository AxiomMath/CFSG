module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCases

public section

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

theorem hyp31 : Hyp31 A := by
  obtain ⟨e⟩ := h.equiv
  have hZ : center ↥A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ center A5 := mem_center_iff.mpr fun y => by
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx y']
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at h1
    exact mem_bot.mpr (e.injective (h1.trans (map_one e).symm))
  exact ⟨h.hyp.standard, hypIIAlt5 ↥A h.hyp.standard.1.1
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩,
    h.oddCore, by have := h.hyp.rank; omega, h.hyp.not_normal⟩

theorem isSimpleGroup_of_rankTwoX_eq_top (hX : rankTwoX A = ⊤) :
    IsSimpleGroup G := by
  obtain ⟨hXF, hXs⟩ := asc08Lemma34 G A h.hyp31
  have h1 : IsSimpleGroup ↥(⊤ : Subgroup G) := by
    rw [← hX]
    show IsSimpleGroup ↥(normalClosure (A : Set G))
    rw [hXF]
    exact hXs
  exact MulEquiv.isSimpleGroup Subgroup.topEquiv.symm

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
