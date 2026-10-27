module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRows
public import CFSG.Sporadic.Recognition.HSMultiplierCert

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

theorem rowBound_HS :
    RowBound .HS :=
  rowBound_of_card_center_le_two rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact CFSG.Sporadic.Recognition.HSMultiplier.card_center_le_two_of_certificate
      (Group.isPerfect_def.2 hq.1) e

end CFSG.EvenSporadicStandard
