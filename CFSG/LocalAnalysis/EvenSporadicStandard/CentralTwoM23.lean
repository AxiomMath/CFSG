module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRows
public import CFSG.Sporadic.Recognition.M23MultiplierCert

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

theorem rowBound_M23 :
    RowBound .M23 :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq _ hs => by
    obtain ⟨e⟩ := hs
    exact Subgroup.eq_bot_of_card_eq _
      (CFSG.Sporadic.Recognition.M23Multiplier.card_center_eq_one_of_certificate
        (Group.isPerfect_def.2 hq.1) e)

end CFSG.EvenSporadicStandard
