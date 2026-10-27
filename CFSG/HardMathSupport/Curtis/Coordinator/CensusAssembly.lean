module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusAssembly
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeAssembly
public import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterIb
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.Glue
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD.Glue
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualTwistedD.Glue
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.Main
public import CFSG.HardMathSupport.Curtis.Proving.FixThreeSmallTwoOrG2

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding

section Three

theorem kFactFixCensusThree_of_proved (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSch : KFactCatalogSchreier) : KFactFixCensusThree :=
  kFactFixCensusThree_of_rest hGA hSch
    (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.fixThreeVoid_b_residual hGA)
    (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.fixThreeVoid_d_residual hGA)
    (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.fixThreeVoid_twistedD_residual hGA)
    CFSG.HardMathSupport.Curtis.Proving.fixThreeVoid_isSmallTwoOrG2

theorem citedBlockThreeAutCenterIb_of_ff (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSch : KFactCatalogSchreier) (hT : CitedBlockTransvectionPLType)
    (hFF : CitedBlockAutCenterFF) : CitedBlockThreeAutCenterIb :=
  citedBlockThreeAutCenterIb_of (kFactFixCensusThree_of_proved hGA hSch) hT hFF

end Three

section PerfThree

theorem citedBlockToralThree_of_triality (hGA : CFSG.Open.GriessAllModelsStatement)
    (hTri : CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixPerfThreeTrialityD)
    (hT : CitedBlockTransvectionPLType) : CitedBlockToralThree :=
  citedBlockToralThree_of_d hGA (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.fixPerfThreeVoid_d hTri) hT

theorem citedBlockThreeAutNine_of_triality (hGA : CFSG.Open.GriessAllModelsStatement)
    (hTri : CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixPerfThreeTrialityD)
    (hT : CitedBlockTransvectionPLType) : CitedBlockThreeAutNine :=
  citedBlockThreeAutNine_of_d hGA (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.fixPerfThreeVoid_d hTri) hT

end PerfThree

end CFSG.HardMathSupport.Curtis.Coordinator
