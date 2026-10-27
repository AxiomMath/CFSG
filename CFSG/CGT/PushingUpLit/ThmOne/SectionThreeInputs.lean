module

public import CFSG.CGT.PushingUpLit.ThmOne.SectionThree
public import CFSG.CGT.PushingUpLit.CGT6K1.Contract
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBAschbacherFive
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoMultiplierRow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEvenCenter
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveM12NotTop
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseI
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenSmall
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltThree
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenFive
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbFinal

public section

namespace CFSG.CGT.PushingUpLit.ThmOne


theorem aschbacherTheoremOneK_of_inputs (hK1 : CGT6K1.StdKernelTwo) (hFoote : CGT6.EndFoote)
    (hK5 : CGT6.StellmacherSixOneThree) : AschbacherTheoremOneK :=
  aschbacherTheoremOneK_holds (CGT6K1.aschbacherEmbeddingK_of_inputs'
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
    hK1
    (fun _ _ t n p f hmodel =>
      CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6Two.griess_all_models_of_twistedE6_two
        CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover.twistedE6TwoMultiplier t n p f hmodel)
    hFoote (ComponentClassification.RankTwoAlt.rankTwoAlternatingStandard_of_open
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
            ComponentClassification.Asc76X.goldschmidtTheoremA)) hK5)

end CFSG.CGT.PushingUpLit.ThmOne
