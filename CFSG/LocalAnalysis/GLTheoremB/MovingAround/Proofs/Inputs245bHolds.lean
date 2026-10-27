module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs245b
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.List
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.AssemblySmall
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.AssemblyLFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRankHolds
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCoverWideHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Out

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245b

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator (sporadicMultipliers_holds)

section Small

theorem input24_5_small_holds
    : Inputs245.Input24_5_small :=
  input24_5_small_of_three
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRank.schurMultiplierRankFact_holds
    (input24_5_smallThree_of_outClosed (input24_5_outClosed_of_outThree
      CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
      (input24_5_outThree_holds
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCover.kFactAlphaListM3Wide_holds
        GL83.I243.smallThreeFacts_holds
        CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
        CFSG.LocalAnalysis.RankThreeTheoremC.kFactSL3OutNormalSylow)))

end Small

section Comp

theorem input24_5_comp_of_compCover_proved (hComp : Input24_5_compCover) : Inputs245.Input24_5_comp := by
  obtain ⟨b⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group .ONan
  exact input24_5_comp_of_cover
    (GL83.I243.pCoverList_of_tables
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput sporadicMultipliers_holds)
    GL83.I243.smallThreeFacts_holds GL83.I243.lFourFacts_holds
    CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
    (CFSG.AGLEmbedding.kFactJ3OuterRank_closed
      (CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group .J3))
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    ((Nat.card_congr b.toEquiv).symm.trans CFSG.Sporadic.ON.card_ON)
    hComp

end Comp

section Proved

theorem input24_5_of_compCover_proved
    (hComp : Input24_5_compCover) : Lemma1211.Input24_5 :=
  Inputs245.input24_5_of_inputs (input24_5_comp_of_compCover_proved hComp) input24_5_small_holds

end Proved

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245b
