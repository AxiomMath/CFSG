module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Member

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

theorem BlockData.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : BlockData X) : BlockData Y := by
  have hZ : (center X).map (e : X →* Y) = center Y := Subgroup.map_center_eq e
  have eq : X ⧸ center X ≃* Y ⧸ center Y :=
    QuotientGroup.congr (center X) (center Y) e hZ
  have hcard : Nat.card ↥(center Y) = Nat.card ↥(center X) := by
    rw [← hZ, Subgroup.card_map_of_injective (f := (e : X →* Y)) e.injective]
  have hM : Nat.card (Open.griessHopfMultiplier (Y ⧸ center Y)) =
      Nat.card (Open.griessHopfMultiplier (X ⧸ center X)) :=
    (Nat.card_congr
      (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eq).toEquiv).symm
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv e h.quasisimple, ?_, ?_, ?_⟩
  · obtain ⟨k, hk1, hk⟩ := h.card_center
    exact ⟨k, hk1, by rw [hcard]; exact hk⟩
  · obtain ⟨τ, n, hm, hs⟩ := h.shape
    exact ⟨τ, n, ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv eq hm, hs⟩
  · rw [hM, hcard]
    exact h.fullCover

end CFSG.OddStandard.HigherRank.F3
