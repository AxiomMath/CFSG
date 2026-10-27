module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Final
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Odd

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem gomiU42Input_holds :
    GomiU42Input :=
  gomiU42Input_of_oddLie gomiU42Selector_oddLie

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
