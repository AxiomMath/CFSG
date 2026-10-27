module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRows
public import CFSG.Sporadic.Recognition.J3MultiplierCert

public section

namespace CFSG.EvenSporadicStandard

theorem rowBound_J3 :
    RowBound .J3 :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact center_eq_bot_of_noPerfectDoubleCover
      CFSG.Sporadic.Recognition.J3Multiplier.noPerfectDoubleCover_nativeJ3_of_certificate hq hZ e

end CFSG.EvenSporadicStandard
