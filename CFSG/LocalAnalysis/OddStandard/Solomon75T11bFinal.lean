module

public import CFSG.LocalAnalysis.OddStandard.Solomon75T11b
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalCert

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

section Ly


theorem solomon44Ly_of_gh74 (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hchk : AhatData.Gen4Good 11 (AhatData.P0 11)) : Solomon44Ly :=
  solomon44Ly_of_leaf (oddCoreElevenThree_of_gh74 hGH hchk)

end Ly

section CaseA


theorem sol_caseA_false_of_gh74 (hGold : CFSG.Goldschmidt.CoreStatement)
    (h34 : Solomon75Lemma34K) (hF : Solomon75Frac53)
    (h55 : Solomon75Lemma55) (h56 : Solomon75Cor56) (h57 : Solomon75Lemma57)
    (h58 : Solomon75Lemma58) (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hchk : AhatData.Gen4Good 11 (AhatData.P0 11)) :
    ∀ (X : Type) [Group X] [Finite X], SolCEx X → HypA X → False :=
  sol_caseA_false_of_leaf hGold h34 hF h55 h56 h57 h58 (oddCoreElevenThree_of_gh74 hGH hchk)

end CaseA

end CFSG.OddStandard.Solomon75
