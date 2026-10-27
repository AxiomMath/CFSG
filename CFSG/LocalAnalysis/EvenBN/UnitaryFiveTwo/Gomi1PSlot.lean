module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PK
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KEight

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem gomiLemma1PInput_holds
    : GomiLemma1PInput :=
  fun X _ _ hK t Y => Gomi1P.gomiLemma1PInputK X hK t Y

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
