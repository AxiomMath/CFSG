module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxMaximality
public import CFSG.Alternating.Multipliers.Main
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCoverMain
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.SolMax

theorem maximalityLemmaInput_of_signalizer
    (hPump : Sol78.AlternatingPumpUpInput) (hSig : GSThmB.SolomonSignalizerInput) :
    Sol78.MaximalityLemmaInput :=
  maximalityLemmaInput_of_inputs hPump (twoGroupAltCoverExclusion_of_inputs hSig
    Alternating.Multipliers.schurAlternatingMultiplierInput hPump)

end CFSG.ComponentClassification.SolMax
