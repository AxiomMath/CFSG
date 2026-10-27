module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDich
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCatHolds
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Asc25Main
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzCoreHolds
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMirrorVanish
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldAscentTop
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldCoreProducer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatL3Holds
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGoldschmidt
public import CFSG.Quasithin.Background.KGSchurMult2Pf
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdEven
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOdd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrl
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwap
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddLeaf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBAschbacherFive

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

section FieldCoreStepAscent

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34FieldCoreStepMirror_of_mirror_ascent
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple) :
    L34FieldCoreStepMirror :=
  l34FieldCoreStepMirror_of_signalizer hS hCI TBLit.griessMultipliersAllModels_holds h13
    (l34FieldSignalizerVanishing_of_mirror_ascent hS h13 l3TwoPowProperFixedCatalog_holds
      Quasithin.schurMult2L3_holds
      (l34FieldSignalizerVanishingMirror_of_inputs hS h13 l3TwoPowProperFixedCatalog_holds
        Quasithin.schurMult2L3_holds goldschmidtStronglyClosedInput_holds))
    (l34FieldCoreOfSignalizer_of_catalog hS hU)

end FieldCoreStepAscent

open CFSG Subgroup

section Dichotomy


theorem l34SuzOddDichotomy_of_residuals
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (hSField : L34FieldStandardExclusion) :
    L34SuzOddDichotomy := by
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
  exact l34SuzOddDichotomy_of_inputs hSch hC4 l3TwoPowProperFixedCatalog_holds
    l34CyclicProperFixedCatalog_holds hU hheld hCI hGA h13 hSV (l34SuzCoreStepMirror_holds hCI h13)
    (l34FieldCoreStepMirror_of_mirror_ascent hSch hU hCI h13) hSField
    (l34SuzEvenStandardExclusion_of_inputs hAS hCIT h25 hSch hC4 hSV) hAS hCIT h25

end Dichotomy

section Exclusion


theorem l34SuzStandardExclusion_of_residuals
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (hSField : L34FieldStandardExclusion) (hZ : L34SuzOddZeroStar) :
    L34SuzStandardExclusion := by
  have hSch := RankThree.PartOne.SPOR.schreierFor_catalog
  have hC4 := suzONanNotProperFixedCatalog_holds
  have hSV : L34SuzSignalizerVanishing := l34SuzSignalizerVanishing_of_steps
    (l34SuzSignalizerGluing_of_facts hSch FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
      KProperRelativeB.heldInput suzSylowFacts_holds twoSuzSylowFacts_holds)
    (l34SuzSignalizerExclusion_of_inputs hC4 goldschmidtStronglyClosedInput_holds hSch hCI
      TBLit.griessMultipliersAllModels_holds h13 suzSylowFacts_holds twoSuzSylowFacts_holds
      suzTypeSylowBound_holds)
  have hAS := RankTwoSporadic.Suz.sporadicCaseOdd_Suz RankTwoFoundation.lemma32
    RankTwoFoundation.lemma33Three
  have h25 := Foote5.Asc25.asc76Lemma25
  have hW : L34SuzOddSwappedExclusion := l34SuzOddSwappedExclusion_of_inputs
    GSThmB.aschbacherTheorem5Input_holds AschbacherKnownGroup.knownGroupFacts_holds
    suzTwoACentralizerAutExtension_holds suzTwoAFusion_holds suzTwoACentralizerFacts_holds
    suzTwoBRootRigidity_holds hZ
  exact l34SuzStandardExclusion_of_even_odd
    (l34SuzEvenStandardExclusion_of_inputs hAS hCIT h25 hSch hC4 hSV)
    (l34SuzOddStandardExclusion_of_inputs hAS hCIT h25
      (l34SuzOddDichotomy_of_residuals hCI h13 hCIT hSField)
      l34SuzOddNormalizerControl_of_inputs hW)

end Exclusion

end CFSG.ComponentClassification.GrSLit.L34Sec5S
