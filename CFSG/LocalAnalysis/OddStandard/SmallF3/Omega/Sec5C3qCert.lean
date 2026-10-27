module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82CorIIIq_of
    (hCI : CFSG.ComponentClassification.GSLit.ClassicalInvolutionInput)
    (hCL1 : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput) :
    Asc82CorIIIq :=
  asc82CorIIIq_of_orders hCI hCL1 CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

end CFSG.OddStandard.SmallF3.Omega
