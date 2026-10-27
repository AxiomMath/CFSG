module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Facts

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def HSLemma21Setting (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop :=
  StdHyp G L ∧ IsSporadic L .HS ∧
    (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
    (∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 → SylowFusion L t) ∧
    ∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 →
      (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ 2

@[expose] def HSSection5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HSLemma21Setting G L → False

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.relIndex_dvd_two_hs
    (F : HSFacts) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : StdHyp G L) (hL : IsSporadic L .HS) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ 2 := by
  have hZ := center_eq_bot_of_isSporadic_hs hL
  have hq : IsSporadic (L ⧸ center L) .HS := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact (h.relIndex_sup_zpowers_dvd (h.card_sylow_eq_two_hs F hL) ht ht2).trans
    (index_dvd_two_of_isSporadic_hs hq)

end CFSG.EvenSporadicStandard.HSStd
