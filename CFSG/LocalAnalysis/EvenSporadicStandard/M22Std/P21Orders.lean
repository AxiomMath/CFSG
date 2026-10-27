module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Gl8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.InputSecondIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std

variable {G : Type} [Group G] [Finite G]

theorem natCard_egaLayer_dvd : Nat.card (egaLayer (G ⧸ fusionOddCore G)) ∣ Nat.card G :=
  (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

theorem false_of_layer_psu52
    (hG : Nat.card G ∣ gl8)
    (h : LieModel (egaLayer (G ⧸ fusionOddCore G)) .PSU 5 2 1) : False := by
  obtain ⟨-, -, hU, -, -⟩ := simple_and_card_of_lieModel _ h (by decide) (Or.inl rfl)
  have hc : Nat.card (egaLayer (G ⧸ fusionOddCore G)) = 13685760 := by
    simpa [CFSG.Open.ordTwistedA, Finset.prod_Icc_succ_top] using hU rfl
  exact not_dvd_gl8_u52 (hc ▸ natCard_egaLayer_dvd.trans hG)

theorem false_of_layer_psu43
    (hG : Nat.card G ∣ gl8)
    (h : LieModel (egaLayer (G ⧸ fusionOddCore G)) .PSU 4 3 1) : False := by
  obtain ⟨-, -, hU, -, -⟩ := simple_and_card_of_lieModel _ h (by decide) (Or.inr rfl)
  have hc : Nat.card (egaLayer (G ⧸ fusionOddCore G)) = 3265920 := by
    simpa [CFSG.Open.ordTwistedA, Finset.prod_Icc_succ_top] using hU rfl
  exact not_dvd_gl8_u43 (hc ▸ natCard_egaLayer_dvd.trans hG)

end CFSG.EvenSporadicStandard.M22Std
