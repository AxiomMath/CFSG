module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModIso
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G1
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4CentCard

public section

namespace CFSG.OddStandard.AltStdSmall4

theorem sec4HTwoPart_holds : Sec4HTwoPart :=
  sec4HTwoPart_of_parts sec4TwoElemN0_holds sec4CentSylowCard_holds sec4ExistsG1Data_holds
    sec4TBFacts_holds

theorem sec4HbarNotSmall_holds : Sec4HbarNotSmall :=
  sec4HbarNotSmall_of_twoPart sec4HTwoPart_holds

end CFSG.OddStandard.AltStdSmall4
