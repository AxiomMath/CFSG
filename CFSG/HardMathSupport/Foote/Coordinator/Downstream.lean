module

public import CFSG.HardMathSupport.Foote.Coordinator.Final
public import CFSG.CGT.PushingUpLit.ThmOne.SectionThreeInputs
public import CFSG.CGT.PushingUpLit.K1R.Dispatch
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.NoA5.Final

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

set_option linter.unusedSectionVars false


theorem aschbacherEmbeddingK_proved : CFSG.CGT.PushingUpLit.CGT6.AschbacherEmbeddingK :=
  CFSG.CGT.PushingUpLit.CGT6K1.aschbacherEmbeddingK_of_inputs'
    CFSG.ComponentClassification.GSThmB.aschbacherTheorem5Input_holds
    CFSG.ComponentClassification.AschbacherKnownGroup.knownGroupFacts_holds
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
    (CFSG.ComponentClassification.Asc75T4.asc75Theorem4_of_steps
      CFSG.ComponentClassification.AschbacherTheorem3.theorem_3_holds
      CFSG.ComponentClassification.AschbacherTheorem5.conclusion_holds
      CFSG.ComponentClassification.Asc75T4.stepConjNormalizer
      CFSG.ComponentClassification.Asc75T4.stepEndgame
      (CFSG.ComponentClassification.Asc75T4.stepRankOne
        CFSG.ComponentClassification.AschbacherTheorem3.theorem_3_holds))
    CFSG.CGT.PushingUpLit.K1R.stdKernelTwo_holds FamilyReduction.griessAllModelsStatement
    endFoote_holds (ComponentClassification.RankTwoAlt.rankTwoAlternatingStandard_of_open
        (ComponentClassification.RankTwoAltFive.altFiveCaseI_of
            (ComponentClassification.RankTwoAlt.altGenerationFive_of
                ComponentClassification.AS76b.asc08Lemma34
                ComponentClassification.Asc76X.goldschmidtTheoremA))
        (ComponentClassification.RankTwoAltFive.asc310EpsOne_of
            ComponentClassification.Asc76X.goldschmidtTheoremA)
        ComponentClassification.RankTwoAltFive.asc310IIb
        ComponentClassification.RankTwoAlt.altFiveM12NotTop_of
        ComponentClassification.RankTwoAlt.altEvenCenterSmall
        ComponentClassification.RankTwoAlt.altThreeCover
        (ComponentClassification.RankTwoAlt.altGenerationSmall_of
            ComponentClassification.AS76b.asc08Lemma34
            ComponentClassification.Asc76X.goldschmidtTheoremA)
        ComponentClassification.RankTwoAlt.altRootFusion
        (ComponentClassification.RankTwoAlt.altTypeTwoFusion_of_rootFusion
            ComponentClassification.RankTwoAlt.altRootFusion)
        (ComponentClassification.RankTwoAlt.altTypeTwoCentralizer
            ComponentClassification.Asc76X.goldschmidtTheoremA))
    CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.stellmacherSixOneThree_holds

theorem aschbacherTheoremOneK_proved : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK :=
  CFSG.CGT.PushingUpLit.ThmOne.aschbacherTheoremOneK_of_inputs
    CFSG.CGT.PushingUpLit.K1R.stdKernelTwo_holds endFoote_holds
    CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.stellmacherSixOneThree_holds

end CFSG.HardMathSupport.Foote.Coordinator
