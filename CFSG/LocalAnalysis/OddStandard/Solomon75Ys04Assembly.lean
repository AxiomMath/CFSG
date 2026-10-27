module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3CenterFree
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DegMain
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FirstMain
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Lemma34K
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5One
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QCert
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapMoveZ
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bCert

public section

namespace CFSG.OddStandard.Solomon75


theorem sol_caseA_false_of_gh74_holds (hGH : ComponentClassification.UFrontier.GH74ModelsInput) :
    ∀ (X : Type) [Group X] [Finite X], SolCEx X → HypA X → False :=
  have hF : Solomon75Frac53 := solomon75Frac53_of_twoComp twoComp_holds
  have hN : Solomon75NoSwap := solomon75NoSwap_of_twoComp twoComp_holds
  sol_caseA_false_of_gh74_of_certificate CFSG.Goldschmidt.coreStatement solomon75Lemma34K hF
    (lemma55 hF hN (lemma54p hF hN (lemma54pNorm hF hN))) cor56 (lemma57_of_certificate hF)
    (lemma58 hF) hGH

theorem solomon2AnInput_of_gh74_of_caseNotA
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (h4 : ∀ (X : Type) [Group X] [Finite X], SolCEx X → ¬ HypA X → False) :
    ComponentClassification.GSThmB.Solomon2AnInput :=
  solomon2AnInput_of_thm11 (solomonThm11_of_cases solLemma31 (sol_caseA_false_of_gh74_holds hGH) h4)

end CFSG.OddStandard.Solomon75
