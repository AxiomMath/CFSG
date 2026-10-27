module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeSmall
public import CFSG.HardMathSupport.Curtis.Coordinator.ToralThreeReduce
public import CFSG.HardMathSupport.Curtis.Coordinator.AutNineReduce
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PerfThreeVoidFull
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB.Main
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeTwistedD.Main

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding


theorem kFactFixCensusPerfThree_of_d (hGA : CFSG.Open.GriessAllModelsStatement)
    (hD : FixPerfThreeVoid (IsLieOf IdxD)) : KFactFixCensusPerfThree :=
  kFactFixCensusPerfThree_of_families fixPerfThreeVoid_A
    CFSG.HardMathSupport.Curtis.UnitaryLevi.fixPerfThreeVoid_twistedA
    (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeB.fixPerfThreeVoid_b hGA) hD
    (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.fixPerfThreeVoid_twistedD hGA)
    fixPerfThreeVoid_g2 (fixPerfThreeSmall (oddCenterRest_of_griess hGA))

theorem citedBlockToralThree_of_d
    (hGA : CFSG.Open.GriessAllModelsStatement) (hD : FixPerfThreeVoid (IsLieOf IdxD))
    (hT : CitedBlockTransvectionPLType) : CitedBlockToralThree :=
  citedBlockToralThree_of_census (kFactFixCensusPerfThree_of_d hGA hD) hT
    (oddCenterRest_of_griess hGA)

theorem citedBlockThreeAutNine_of_d (hGA : CFSG.Open.GriessAllModelsStatement)
    (hD : FixPerfThreeVoid (IsLieOf IdxD)) (hT : CitedBlockTransvectionPLType) :
    CitedBlockThreeAutNine :=
  citedBlockThreeAutNine_of_census (kFactFixCensusPerfThree_of_d hGA hD) hT

end CFSG.HardMathSupport.Curtis.Coordinator
