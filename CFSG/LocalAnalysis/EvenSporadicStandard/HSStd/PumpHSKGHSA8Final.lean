module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSKGHSA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSCatalog

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

theorem kgHSA8_proved :
  KGHSA8 := by
  intro K _ _ hcat _ hcard A hA
  exact kgHSA8_of_sporadic hs100Model (isSporadic_HS_of_catalog hcat hcard) A hA

end CFSG.EvenSporadicStandard.HSStd.PumpHS
