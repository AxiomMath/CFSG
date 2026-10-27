module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov5
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov6

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def HaradaSolomon08M22Split : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G),
    standardComponentOddCore G = ⊥ → standardComponentIsStandard L →
    IsSporadic (L ⧸ center L) .M22 → orderOf t = 2 → (center L).map L.subtype = zpowers t →
    centralizer ({t} : Set G) = normalizer (L : Set G) →
    L.relIndex (centralizer ({t} : Set G)) = 2 →
    (∃ y ∈ centralizer ({t} : Set G), y ∉ L ∧ orderOf y = 2) → L.Normal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_split (hSplit : HaradaSolomon08M22Split) (h : StdHyp G L) {t : G}
    (hc : CoverSetting L t) (hq : IsSporadic (L ⧸ center L) .M22)
    (hrel : L.relIndex (centralizer ({t} : Set G)) = 2)
    (hy : ∃ y ∈ centralizer ({t} : Set G), y ∉ L ∧ orderOf y = 2) : False := by
  have := h.simple
  have hodd : standardComponentOddCore G = ⊥ :=
    standardComponentOddCore_eq_bot_of_simple (even_card_of_stdHyp h)
  have hnorm : L.Normal :=
    hSplit G L t hodd h.standard hq hc.orderOf_t hc.map_center hc.centralizer_t hrel hy
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with h0 | h0
  · exact StdHyp_ne_bot h h0
  · exact h.ne_top h0

theorem false_of_center_ne_bot_of_cases
    (h25 : Finkelstein77.Asc76Lemma25) (hSplit : HaradaSolomon08M22Split)
    (hTw : M22TwistedSylowData) (h : StdHyp G L) (hq : IsSporadic (L ⧸ center L) .M22)
    (hZ : center L ≠ ⊥) : False := by
  obtain ⟨t, hc⟩ := exists_coverSetting h25 h hq hZ
  rcases coverSetting_cases hc with hH | ⟨hrel, hno⟩ | ⟨hrel, hy⟩
  · exact false_of_inner_cover h hc hq hH
  · exact false_of_twisted hTw h hc hq hrel hno
  · exact false_of_split hSplit h hc hq hrel hy

end CFSG.EvenSporadicStandard.M22Std
