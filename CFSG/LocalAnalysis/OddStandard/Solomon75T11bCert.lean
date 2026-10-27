module

public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bFinal
public import Certificates.Certificate6132

public section

open CFSG.OddStandard.Solomon75.AhatData

namespace CFSG.OddStandard.Solomon75

section B

theorem solomon44Ly_of_gh74_of_certificate
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput) : Solomon44Ly :=
  solomon44Ly_of_gh74 hGH Certificates.certificate6132.2

end B

section C

theorem sol_caseA_false_of_gh74_of_certificate (hGold : CFSG.Goldschmidt.CoreStatement)
    (h34 : Solomon75Lemma34K) (hF : Solomon75Frac53)
    (h55 : Solomon75Lemma55) (h56 : Solomon75Cor56) (h57 : Solomon75Lemma57)
    (h58 : Solomon75Lemma58) (hGH : ComponentClassification.UFrontier.GH74ModelsInput) :
    ∀ (X : Type) [Group X] [Finite X], SolCEx X → HypA X → False :=
  sol_caseA_false_of_gh74 hGold h34 hF h55 h56 h57 h58 hGH Certificates.certificate6132.2

end C

end CFSG.OddStandard.Solomon75
