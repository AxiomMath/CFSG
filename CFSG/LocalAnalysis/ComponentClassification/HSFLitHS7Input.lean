module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7Families
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitFinalA7
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapMain
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bInputsLit
public import CFSG.LocalAnalysis.OddStandard.Harada75

public section

namespace CFSG.ComponentClassification.HSFLit.HS7

theorem harrisSolomonA7Input_of_inputs
    (hGH : UFrontier.GH74ModelsInput) (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hAlt : SolMax.AltPumpSporadicClause) : GSThmB.HarrisSolomonA7Input := by
  intro G _ _ hKP hF t ht L hLt hL h7 hcyc
  exact harrisSolomonA7_of_facts
    (hsflitA7_of_inputs hGH OddStandard.Harada75.haradaInput_holds Sec8.fritz812dNotSylow)
    (hs7OddLieFact_of_inputs hGLS CatLeafProof.lieOrderFormulasInput)
    (hs7OuterFact_of_inputs hGLS hAlt) hKP hF ht hLt hL h7 hcyc

end CFSG.ComponentClassification.HSFLit.HS7
