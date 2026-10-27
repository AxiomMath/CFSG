module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCatalogueU
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGoldschmidt
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatSuzHolds
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34ONanCoreStepMirror_holds
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple) :
    L34ONanCoreStepMirror :=
  l34ONanCoreStepMirror_of_signalizer RankThree.PartOne.SPOR.schreierFor_catalog hCI
    TBLit.griessMultipliersAllModels_holds h13
    (l34ONanSignalizerVanishing_of_inputs suzONanNotProperFixedCatalog_holds
      GrSLit.goldschmidtStronglyClosedInput_holds RankThree.PartOne.SPOR.schreierFor_catalog hCI
      TBLit.griessMultipliersAllModels_holds h13)
    (l34ONanCoreOfSignalizer_of_catalog RankThree.PartOne.SPOR.schreierFor_catalog
      FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds KProperRelativeB.heldInput)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
