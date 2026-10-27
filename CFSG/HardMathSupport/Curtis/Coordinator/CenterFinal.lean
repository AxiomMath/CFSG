module

public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Main
public import CFSG.HardMathSupport.Curtis.Coordinator.FFToralMain
public import CFSG.HardMathSupport.Curtis.Coordinator.CensusAssembly
public import CFSG.HardMathSupport.Curtis.Proving.ShortBlockBridge
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterFinal

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding

theorem citedBlockThreeAutCenterIb_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) (hSch : KFactCatalogSchreier)
    (hT : CitedBlockTransvectionPLType) : CitedBlockThreeAutCenterIb :=
  citedBlockThreeAutCenterIb_of_ff hGA hSch hT
      (citedBlockAutCenterFF_of_sl3
          CFSG.HardMathSupport.Curtis.Proving.shortBlockCommutatorCentre_of_step
          (citedBlockAutCenterFFSL3_holds hGA))

theorem citedBlockToralThreeCenter_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : CitedBlockToralThreeCenter :=
  citedBlockToralThreeCenter_of_ff hGA (citedBlockToralCenterFF_holds hGA)

end CFSG.HardMathSupport.Curtis.Coordinator
