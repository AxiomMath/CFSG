module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatL3Asm
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

theorem l3TwoPowProperFixedCatalog_holds :
    L3TwoPowProperFixedCatalog :=
  l3TwoPowProperFixedCatalog_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
    CatLeafProof.lieOrderFormulasInput CatLeafProof.monsterInnerInput
    CatLeafProof.monsterLocalComponentsInput

end CFSG.ComponentClassification.GrSLit.L34Sec5S
