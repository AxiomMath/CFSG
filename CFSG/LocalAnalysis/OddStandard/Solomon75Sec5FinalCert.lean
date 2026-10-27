module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalAssembly
public import CFSG.LocalAnalysis.OddStandard.Solomon75NineTen
public import CFSG.LocalAnalysis.OddStandard.Solomon75LyLeaf

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

section Aschbacher

theorem alternatingBalanceData_of_certificates
    (m : ℕ) (h8 : 8 ≤ m) (h11 : m ≤ 11) :
    AlternatingBalanceData m := by
  have hm : m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 := by omega
  rcases hm with rfl | rfl | rfl | rfl
  · exact alternatingBalanceData_eight_of_certificate
  · exact alternatingBalanceData_nine_of_certificate
  · exact alternatingBalanceData_ten_of_certificate
  · exact alternatingBalanceData_eleven_of_certificate


theorem sol_caseA_false_of_certificates (hGold : CFSG.Goldschmidt.CoreStatement)
    (h34 : Solomon75Lemma34K) (hF : Solomon75Frac53)
    (h55 : Solomon75Lemma55) (h56 : Solomon75Cor56) (h57 : Solomon75Lemma57)
    (h58 : Solomon75Lemma58) (h44Ly : Solomon44Ly) :
    ∀ (X : Type) [Group X] [Finite X], SolCEx X → HypA X → False :=
  sol_caseA_false hGold h34 hF h55 h56 h57 h58 alternatingBalanceData_of_certificates
    solomon44McL_of_certificate h44Ly solomon44NineTen_of_certificate


theorem sol_caseA_false_of_leaf (hGold : CFSG.Goldschmidt.CoreStatement)
    (h34 : Solomon75Lemma34K) (hF : Solomon75Frac53)
    (h55 : Solomon75Lemma55) (h56 : Solomon75Cor56) (h57 : Solomon75Lemma57)
    (h58 : Solomon75Lemma58) (hleaf : OddCoreElevenThree) :
    ∀ (X : Type) [Group X] [Finite X], SolCEx X → HypA X → False :=
  sol_caseA_false_of_certificates hGold h34 hF h55 h56 h57 h58 (solomon44Ly_of_leaf hleaf)

end Aschbacher

end CFSG.OddStandard.Solomon75
