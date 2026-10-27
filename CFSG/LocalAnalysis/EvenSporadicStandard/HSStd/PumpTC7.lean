module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7HS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7L39
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7L43
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Prod
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.TC7U43Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Catalog

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

theorem threeCentralizer7_of_u43
    (hU : ThreeCentralizer7U43) : ThreeCentralizer7 := by
  intro Γ _ _ N hN hC hcases y hy
  have := hN
  have hdvd : Nat.card ↥(centralizer ({y} : Set Γ)) ∣ Nat.card Γ :=
    Subgroup.card_subgroup_dvd_card _
  rcases hcases with he | hHS | hU43 | hL39 | hL43
  · obtain ⟨e⟩ := he
    exact fun h7 => not_seven_dvd_card_of_prod N hC e (h7.trans hdvd)
  · exact not_seven_dvd_centralizer_of_hs hs100Model N hC hHS hy
  · exact hU Γ N hN hC hU43 y hy
  · exact not_seven_dvd_centralizer_of_l39 N hC hL39 hy
  · exact fun h7 => not_seven_dvd_card_of_l43 N hC hL43 (h7.trans hdvd)

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
