module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzGlue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzSylowFactsHolds
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzVExclusion
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGoldschmidt

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

theorem l34SuzCoreStepMirror_of_exclusion
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts) (hV : L34SuzSignalizerExclusion) :
    L34SuzCoreStepMirror :=
  have hG := l34SuzSignalizerGluing_of_facts RankThree.PartOne.SPOR.schreierFor_catalog
    FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds KProperRelativeB.heldInput hF1 hF2
  l34SuzCoreStepMirror_of_signalizer RankThree.PartOne.SPOR.schreierFor_catalog hCI
    TBLit.griessMultipliersAllModels_holds h13 (l34SuzSignalizerVanishing_of_steps hG hV)
    (l34SuzCoreOfSignalizer_of_steps hG l34TwoSuzCoreOfSignalizer_holds)

theorem l34SuzCoreStepMirror_of_suzExclusion
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hV : L34SuzSignalizerExclusion) : L34SuzCoreStepMirror :=
  l34SuzCoreStepMirror_of_exclusion hCI h13 suzSylowFacts_holds twoSuzSylowFacts_holds hV

theorem l34SuzCoreStepMirror_holds
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple) :
    L34SuzCoreStepMirror :=
  l34SuzCoreStepMirror_of_suzExclusion hCI h13
    (l34SuzSignalizerExclusion_of_inputs suzONanNotProperFixedCatalog_holds
      GrSLit.goldschmidtStronglyClosedInput_holds RankThree.PartOne.SPOR.schreierFor_catalog hCI
      TBLit.griessMultipliersAllModels_holds h13 suzSylowFacts_holds twoSuzSylowFacts_holds
      suzTypeSylowBound_holds)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
