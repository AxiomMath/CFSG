module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelUnitary

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

theorem benderBorelFactsHold : BenderBorelFactsHold :=
  benderBorelFactsHold_of_models psl2BorelFacts suzukiBorelFacts unitaryBorelFacts

end CFSG.ProperTwoGeneratedCore.TheoremC
