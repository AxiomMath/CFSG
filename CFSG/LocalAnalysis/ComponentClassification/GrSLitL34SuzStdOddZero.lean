module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroStar
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroConfig
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroSuz
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

theorem l34SuzOddZeroStar_of_inputs
    (hcat : L34CyclicProperFixedCatalog)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hC4 : SuzONanNotProperFixedCatalog) (hSV : L34SuzSignalizerVanishing)
    (hC : L34SuzOddNormalizerControl) (hSG : SuzTwoBFusionGeneration)
    (hC5 : L3TwoPowProperFixedCatalog) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h13 : Sol76T13.SolomonThm13Simple)
    (hCSuz : L34SuzCoreStepMirror) (hCField : L34FieldCoreStepMirror)
    (hSField : L34FieldStandardExclusion) (hEven : L34SuzEvenStandardExclusion)
    (hAS : RankTwoSporadic.SporadicCaseOdd .Suz)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (h25 : EvenSporadicStandard.Finkelstein77.Asc76Lemma25) :
    L34SuzOddZeroStar := by
  intro G _ _ A V K t y P hc hS hD hne hK hV _ hodd hcomp
  exact star_of_l34PartnerConfig hcat hSch hU hheld hS.base
    (l34ZeroHostFree_of_inputs hC hSG hSch hC4 hC5 hCI hGA h13 hCSuz hCField hSField hEven hAS
      hCIT h25 hS.base)
    (l34PartnerConfig_of_l34SuzOddZero hSch hC4 hSV hS hD hc hne hK hV hodd hcomp)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
