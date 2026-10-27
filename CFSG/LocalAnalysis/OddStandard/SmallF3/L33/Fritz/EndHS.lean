module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.BridgeHyp
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGHCert
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.OddStandard.SmallF3.L33

open Subgroup CFSG.ComponentClassification.HSFLit

theorem thirteen_dvd_card {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}
    (h : FritzHyp X t L) : 13 ∣ Nat.card X := by
  have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three
    (h.model.statedClassicalModel_of_ne_zero (by norm_num))
  have h2 : Nat.card L ∣ Nat.card X := L.card_subgroup_dvd_card
  rw [h1] at h2
  exact (by norm_num : 13 ∣ 5616).trans h2

theorem false_of_ghRel_sylow
    (hGH : GorensteinHarrisInput) {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X}
    {L : Subgroup X} (h : FritzHyp X t L)
    (hS : ∃ (P : Sylow 2 X) (z l α₁ α₂ α₃ α₄ x y a : X), GHRel z l α₁ α₂ α₃ α₄ x y a ∧
      Subgroup.closure ({z, l, α₁, α₂, α₃, α₄, x, y, a} : Set X) = P ∧
        Nat.card (P : Subgroup X) = 512) : False := by
  obtain ⟨S, z, l, α₁, α₂, α₃, α₄, x, y, a, hrel, hgen, hcard⟩ := hS
  obtain ⟨e⟩ := gorensteinHarris_corollaryA hGH
    (isTypeHS_of_ghRel ghPresentationBound ghRelInHS S hrel hgen hcard)
  have h13 := thirteen_dvd_card h
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HS.card_HS] at h13
  omega

end CFSG.OddStandard.SmallF3.L33
