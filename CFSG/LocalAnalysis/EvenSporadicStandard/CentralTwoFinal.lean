module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoAssembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoHN

public section

namespace CFSG.EvenSporadicStandard

theorem centralTwoBound
    : CentralTwoBound :=
  centralTwoBound_of_rowBound_HN rowBound_HN

end CFSG.EvenSporadicStandard
