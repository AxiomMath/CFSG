module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LMain
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UMain
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Red

public section


namespace CFSG.ComponentClassification.HarrisLit.P1

theorem p1Models : P1Models := fun _ _ h =>
  h.elim L43.p1ModelFacts_of_lieModel_psl U43.p1ModelFacts_of_lieModel_psu

theorem l4U4ThreeInvolutionFacts : L4U4ThreeInvolutionFacts :=
  l4U4ThreeInvolutionFacts_of_models p1Models

end CFSG.ComponentClassification.HarrisLit.P1
