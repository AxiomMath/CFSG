module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem StdHyp.center_eq_bot (h : StdHyp G L) : center G = ⊥ := by
  have := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonabelian
    exact hab (mem_center_iff.1 (h1 ▸ mem_top b) a)

theorem StdHyp.isKGroupCat_of_ne_top (h : StdHyp G L) {P : Subgroup G} (hP : P ≠ ⊤) :
    CFSG.SectionRank.IsKGroupCat P :=
  CFSG.QuasithinUnique.isKGroupCat_of_kProper h.kProper hP

theorem StdHyp.isKGroupCat_centralizer (h : StdHyp G L) {β : G} (hβ : β ≠ 1) :
    CFSG.SectionRank.IsKGroupCat ↥(centralizer ({β} : Set G)) := by
  refine h.isKGroupCat_of_ne_top fun htop => hβ ?_
  have hβc : β ∈ center G := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({β} : Set G) := htop ▸ mem_top g
    exact mem_centralizer_singleton_iff.1 hg
  rwa [h.center_eq_bot, mem_bot] at hβc

theorem StdHyp.isKGroupCat_centralizer_of_orderOf (h : StdHyp G L) {β : G} {n : ℕ} (hn : 2 ≤ n)
    (hβ : orderOf β = n) : CFSG.SectionRank.IsKGroupCat ↥(centralizer ({β} : Set G)) :=
  h.isKGroupCat_centralizer fun h1 => by
    rw [h1, orderOf_one] at hβ
    omega

theorem StdHyp.isKGroupCat_normalizer (h : StdHyp G L) {E : Subgroup G} (hE : E ≠ ⊥)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    CFSG.SectionRank.IsKGroupCat ↥(normalizer (E : Set G)) := by
  have := h.simple
  refine h.isKGroupCat_of_ne_top fun htop => ?_
  have hn : E.Normal := normalizer_eq_top_iff.1 htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal E with h1 | h1
  · exact hE h1
  · obtain ⟨a, b, hab⟩ := h.nonabelian
    exact hab (hcomm a (h1 ▸ mem_top a) b (h1 ▸ mem_top b))

end CFSG.EvenSporadicStandard
