module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafHeMainFi24
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.Monster.SteinbergMSporadicOddCoreFree

public section

namespace CFSG.ComponentClassification.GrSLit


theorem heldNotProperFixedInput_holds : HeldNotProperFixedInput :=
  CFSG.ComponentClassification.CatLeaf.heldNotProperFixedInput_of_inputs'
    CFSG.SeitzReduction.gls3OddLieAutComponentsInput
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.ComponentClassification.CatLeafProof.evenLieOuterTwoComponentsInput_holds
    CFSG.ComponentClassification.CatLeafProof.monsterInnerInput
    CFSG.ComponentClassification.CatLeafProof.monsterLocalComponentsInput
    CFSG.ComponentClassification.CatalogueU.sporadicOddCoreFree_M

end CFSG.ComponentClassification.GrSLit
