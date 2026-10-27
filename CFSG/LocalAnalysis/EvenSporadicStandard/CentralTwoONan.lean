module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRows
public import CFSG.Sporadic.Recognition.ONMultiplierCert

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

theorem rowBound_ONan :
    RowBound .ONan :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact CFSG.Sporadic.Recognition.ONMultiplier.center_eq_bot_of_certificate
      (Group.isPerfect_def.2 hq.1) hZ e

end CFSG.EvenSporadicStandard
