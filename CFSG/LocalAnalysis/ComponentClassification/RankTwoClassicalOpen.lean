module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalHypIIFinal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSymplecticOut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpCase1Type
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitaryPerf
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222SpPairBC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthATwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcU4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222SpTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthCaseTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222UnitaryTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYStep75
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYStep76
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44Endgame
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44J2Cert
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44M12
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpO2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcSp6
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidPlusChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbFinal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinAll
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsOut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsCharTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzL34Diag

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoSporadic

theorem rankTwoClassicalEvenStandard_of_open
    (hBender : RankTwoBenderStandard) (hL3 : RankTwoL3EvenStandard) :
    RankTwoClassicalEvenStandard := by
  have h32 := RankTwoFoundation.lemma32
  have h33 := RankTwoFoundation.lemma33Three
  have h4 := RankTwoFoundation.asc75Theorem4
  have h2 := RankTwoFoundation.asc76Theorem2
  have h34 := AS76b.asc08Lemma34
  have h310 := RankTwoAltFive.asc08Lemma310
  have hF : Classical222Facts := by
    refine ⟨fun fam => ?_, fun fam => ?_, fun fam => ?_, symplecticJ23, orthJ4⟩
    · cases fam
      exacts [deltaAlpha_linear, deltaAlpha_unitary, deltaAlpha_symplectic, deltaAlpha_orthPlus,
        deltaAlpha_orthMinus]
    · cases fam
      exacts [autAlpha_linear, autAlpha_unitary, autAlpha_symplectic, autAlpha_orthPlus,
        autAlpha_orthMinus]
    · cases fam
      exacts [pairOrbitFree_linear, pairOrbitFree_unitary, pairOrbitFree_symplectic,
        pairOrbitFree_orthPlus, pairOrbitFree_orthMinus]
  have h222 := classical222Large_of hF
  have I : Inputs74 := ⟨h32, h4, h34, h2, classicalOutCommOdd, classicalCentralizerCharTwo,
    h222, classicalJSylow_of hF⟩
  have hExc := classical222TwoExcCenter_of exc213_PSU_four exc213_PSU_six exc213_PSp_three
    exc213_POmegaPlus_four
  have hTwo := classical222Two_of hExc deltaAlphaTwo_symplectic deltaAlphaTwo_orthPlus
    deltaAlphaTwo_orthMinus symplecticJ23Two orthJ4Two
    (classical222TwoB_of linearCaseIITwo unitaryCaseIITwo orthCaseIITwo)
  have h73 := step73_of I h33 hTwo linearTwoResidual symplecticTwoOut
  have h74 := step74_of I classicalSplit classicalPrimaryPerfect h33 h73 symplecticTypeAPerfect
    symplecticCase1Type symplecticSplitA symplecticPairA2
  have hRC : ClassicalRigidChoice := ⟨rigidLeviChoice_linear, rigidLeviChoice_unitary,
    rigidLeviChoice_orthPlus,
    rigidLeviChoice_orthMinus⟩
  have h75 := step75Y_of h32 h4 h34 h2 classicalOutCommOdd classicalCentralizerCharTwo h222
    hRC symplecticYChoice symplecticOddCentralizerO2
  have h76 := step76Y_of_certs hBender hL3 RankTwoExceptional.suzL34DiagInput h4 h32 h34 h310
    (sp44Endgame_of h32 h310 J2Std.j2A4Facts m12AutThreeFive)
  exact rankTwoClassicalEvenStandard_of_stepsY
    (classicalHypII_of_multiplier classicalEvenMultiplier) h74 h75 h76

end CFSG.ComponentClassification.RankTwoClassical
