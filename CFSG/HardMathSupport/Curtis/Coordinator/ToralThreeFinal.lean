module

public import CFSG.HardMathSupport.Curtis.Coordinator.CensusAssembly
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeTriality
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeTrialityFlag

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding

theorem citedBlockToralThree_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) (hT : CitedBlockTransvectionPLType) :
    CitedBlockToralThree :=
  citedBlockToralThree_of_triality hGA
    (fixPerfThreeTrialityD (oddCenterRest_of_griess hGA) trialityFlagInput) hT

theorem citedBlockThreeAutNine_holds (hGA : CFSG.Open.GriessAllModelsStatement)
    (hT : CitedBlockTransvectionPLType) : CitedBlockThreeAutNine :=
  citedBlockThreeAutNine_of_triality hGA
    (fixPerfThreeTrialityD (oddCenterRest_of_griess hGA) trialityFlagInput) hT

end CFSG.HardMathSupport.Curtis.Coordinator
