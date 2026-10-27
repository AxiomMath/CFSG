module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Cent
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Pgl

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

theorem l4U4ThreeInvolutionFacts_of_models (hM : P1Models) : L4U4ThreeInvolutionFacts :=
  ⟨cent_of_models hM, pgl_of_models hM⟩

end CFSG.ComponentClassification.HarrisLit.P1
