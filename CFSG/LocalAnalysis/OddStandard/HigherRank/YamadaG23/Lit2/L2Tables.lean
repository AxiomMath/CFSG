module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Odd
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.SporadicTable
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

@[expose] def L2Tables : Prop :=
  CFSG.ComponentClassification.HarrisLit.T1.P54.GriessNativeTable ∧
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.NativeSporadicMultipliers ∧
    CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput

end CFSG.OddStandard.HigherRank.YamadaG23
