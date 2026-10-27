module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenOneThreeRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCoverWideHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentre
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBFrontier

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo

theorem sevenOneThreeRankTwo_holds : SevenOneThreeRankTwo :=
  sevenOneThreeRankTwo_of_kFacts KFactProofs.Stroth.AlmostSimple.exceptionalTowers
    KFactProofs.Stroth.TripleCover.kFactAlphaListM3Wide_holds
    (KFactProofs.T29.noncyclicCentreRank_of_tables
        (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
        (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
            CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))

end CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo
