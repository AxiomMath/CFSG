module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdResidual
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZero

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup


theorem l34SuzStandardExclusion_of_four_residuals
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (hSField : L34FieldStandardExclusion) :
    L34SuzStandardExclusion := by
  have hSch := RankThree.PartOne.SPOR.schreierFor_catalog
  have hC4 := suzONanNotProperFixedCatalog_holds
  have hU := FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
  have hheld := KProperRelativeB.heldInput
  have hGA := TBLit.griessMultipliersAllModels_holds
  have hSV : L34SuzSignalizerVanishing := l34SuzSignalizerVanishing_of_steps
    (l34SuzSignalizerGluing_of_facts hSch hU hheld suzSylowFacts_holds twoSuzSylowFacts_holds)
    (l34SuzSignalizerExclusion_of_inputs hC4 goldschmidtStronglyClosedInput_holds hSch hCI hGA h13
      suzSylowFacts_holds twoSuzSylowFacts_holds suzTypeSylowBound_holds)
  have hAS := RankTwoSporadic.Suz.sporadicCaseOdd_Suz RankTwoFoundation.lemma32
    RankTwoFoundation.lemma33Three
  have h25 := Foote5.Asc25.asc76Lemma25
  exact l34SuzStandardExclusion_of_residuals hCI h13 hCIT hSField
    (l34SuzOddZeroStar_of_inputs l34CyclicProperFixedCatalog_holds hSch hU hheld hC4 hSV
      l34SuzOddNormalizerControl_of_inputs suzTwoBFusionGeneration_holds
      l3TwoPowProperFixedCatalog_holds hCI hGA h13 (l34SuzCoreStepMirror_holds hCI h13)
      (l34FieldCoreStepMirror_of_mirror_ascent hSch hU hCI h13) hSField
      (l34SuzEvenStandardExclusion_of_inputs hAS hCIT h25 hSch hC4 hSV) hAS hCIT h25)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
