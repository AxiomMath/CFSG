module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafHeMain

public section

namespace CFSG.ComponentClassification.CatLeaf

theorem heldNotProperFixedInput_of_inputs' (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hEO : EvenLieOuterTwoComponentsInput)
    (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    (oM : CatalogueU.SporadicOddCoreFree .M) : GrSLit.HeldNotProperFixedInput :=
  heldNotProperFixedInput_of_inputs hGLS hO hEO
    Sporadic.FischerOddCore.fi24primeOuterComponentsInput_holds hMinn hMcomp oM

end CFSG.ComponentClassification.CatLeaf
