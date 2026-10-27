module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRows
public import CFSG.Sporadic.Recognition.Co2MultiplierCert

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

theorem rowBound_Co2 :
    RowBound .Co2 :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact Subgroup.eq_bot_of_card_eq _ (card_eq_one_of_odd hZ (Odd.of_dvd_nat (by decide)
      (CFSG.Sporadic.Recognition.Co2Multiplier.card_center_dvd_three_of_certificate
        (Group.isPerfect_def.2 hq.1) e)))

end CFSG.EvenSporadicStandard
