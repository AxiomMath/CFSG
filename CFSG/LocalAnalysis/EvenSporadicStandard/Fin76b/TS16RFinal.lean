module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUMain

public section

namespace CFSG.EvenSporadicStandard.Fin76b

theorem fin76bOuterS16Loc_holds :
    Fin76bOuterS16Loc :=
  fin76bOuterS16Loc_of_kbarFacts fin76bS16KBar

end CFSG.EvenSporadicStandard.Fin76b
