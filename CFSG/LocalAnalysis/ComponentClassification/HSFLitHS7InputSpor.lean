module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7Input
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSpor

public section

namespace CFSG.ComponentClassification.HSFLit.HS7

theorem harrisSolomonA7Input_of_residues
    (hGH : UFrontier.GH74ModelsInput) (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hSuz : SolMax.SuzOuterComponentsInput) (hON : SolMax.ONOuterComponentsInput) :
    GSThmB.HarrisSolomonA7Input :=
  harrisSolomonA7Input_of_inputs hGH hGLS (SolMax.altPumpSporadicClause_of_inputs hSuz hON)

end CFSG.ComponentClassification.HSFLit.HS7
