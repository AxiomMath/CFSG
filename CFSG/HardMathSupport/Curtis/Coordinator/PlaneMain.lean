module

public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneCyc
public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneOdd
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.HardMathSupport.Curtis.Coordinator.RosterToral

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding


theorem kFactBlockPlaneIb_holds (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSch : KFactCatalogSchreier) : KFactBlockPlaneIb :=
  Plane.kFactBlockPlaneIb_of_odd
    (Plane.kFactBlockPlaneIbOdd_of (kFactFixCensusPrime_of_proved hGA hSch))

theorem citedBlockToralCycAut_holds (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSch : KFactCatalogSchreier) (hTPLT : CitedBlockTransvectionPLType) :
    CitedBlockToralCycAut :=
  Plane.citedBlockToralCycAut_of_census (kFactFixCensusPrime_of_proved hGA hSch)
    (citedBlockTransvectionPL_of_type hTPLT)

end CFSG.HardMathSupport.Curtis.Coordinator
