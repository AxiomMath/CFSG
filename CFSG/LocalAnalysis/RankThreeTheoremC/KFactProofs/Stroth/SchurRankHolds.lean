module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRankMain
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRank

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator (sporadicMultipliers_holds)


theorem schurMultiplierRankFact_holds : SchurMultiplierRankFact :=
  schurMultiplierRankFact_of_tables
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput sporadicMultipliers_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRank
