module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterMain
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadical

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding


theorem citedBlockToralThreeCenterFix_holds
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSch : KFactCatalogSchreier) : CitedBlockToralThreeCenterFix :=
  citedBlockToralThreeCenterFix_of (kFactFixCensusCenter_holds hGA) (glueVhyp_of_schreier hSch)

theorem citedBlockToralThreeCenter_of_ff (hGA : CFSG.Open.GriessAllModelsStatement)
    (hFF : CitedBlockToralCenterFF) : CitedBlockToralThreeCenter :=
  citedBlockToralThreeCenter_of (kFactFixCensusCenter_holds hGA) hFF

end CFSG.HardMathSupport.Curtis.Coordinator
