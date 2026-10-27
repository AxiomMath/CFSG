module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky


theorem l2Sporadic_holds :
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.NativeSporadicMultipliers :=
  Coordinator.nativeSporadicMultipliers_of_ledger
    (fun s hs _ hp hp5 _ => Proving.kernelTrivialAt_carrier_of_five_le
      CFSG.RankThree.PartOne.MultRes.sporadicResidualKernelsTrim_holds s hs hp hp5)
    Coordinator.sporadicOpenCells_holds

end CFSG.OddStandard.HigherRank.YamadaG23
