module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCoverWide
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCover

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator (sporadicMultipliers_holds)

theorem kFactAlphaListM3Wide_holds : KFactAlphaListM3Wide :=
  kFactAlphaListM3Wide_of_tables
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement sporadicMultipliers_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCover
