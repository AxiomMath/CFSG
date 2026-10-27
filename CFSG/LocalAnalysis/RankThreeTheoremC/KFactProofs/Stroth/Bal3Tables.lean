module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Discharge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResSL3
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator (sporadicMultipliers_holds)

theorem bal3ThreeCenter_holds : Bal3ThreeCenter :=
  bal3ThreeCenter_of_tables CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput sporadicMultipliers_holds

theorem bal3ThreeSL3_holds : Bal3ThreeSL3 :=
  bal3ThreeSL3_of_tables CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput sporadicMultipliers_holds

theorem bal3KFacts_of_open' (hK : SchurMultiplierRankFact) (hW : KFactAlphaListM3Wide)
    (hO : ONanSylowThreeDatum) (h294 : Input29_4Rank3) : Bal3KFacts :=
  bal3KFacts_of_open hK hW bal3ThreeCenter_holds hO bal3ThreeSL3_holds h294

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
