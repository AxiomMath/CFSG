module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.FixPrimeCycD
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusAssembly

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding

theorem kFactFixCensusPrime_of_proved
    (hGA : CFSG.Open.GriessAllModelsStatement) (hSch : KFactCatalogSchreier) :
    KFactFixCensusPrime :=
  kFactFixCensusPrime_of_rest hGA hSch
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.fixPrimeCycTorus_d
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.fixPrimeCycTorus_twistedD

end CFSG.HardMathSupport.Curtis.Coordinator
