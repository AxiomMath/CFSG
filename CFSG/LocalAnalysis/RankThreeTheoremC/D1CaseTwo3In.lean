module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoIn
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NoSPDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}

theorem D1CaseTwoData3.false_of_in_three (hd : D1CaseTwoData3 3 P M H R Rbar)
    (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hSyl : KFactCaseTwoSylow) (hSch : KFactCatalogSchreier)
    (hAT : KFactCaseTwoAlphaThree) (hnosp : D1CaseTwoNoSP 3 M H R)
    (hin : ∃ z : H, D1CaseTwoCand 3 M H R z ∧ ¬ D1CzOutside 3 (z : G)) : False :=
  D1CaseTwoDataAt.false_of_in_three (hd := hd.toAt) (hAut := (kFactCycAut_of_kFactOutCyclic hOut))
    (hS := hS) (hSyl := hSyl) (hSch := hSch) (hAT := hAT) (hnosp := hnosp) (hin := hin)

end Data

theorem d1CaseTwoPosZeroInThree_of {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hSyl : KFactCaseTwoSylow) (hSch : KFactCatalogSchreier) (hAT : KFactCaseTwoAlphaThree) :
    D1CaseTwoPosZeroInThree G := by
  intro P M H R Rbar hd hnosp hin
  intros
  exact D1CaseTwoData3.false_of_in_three hd hOut hS hSyl hSch hAT hnosp hin

theorem d1CaseTwoNTwoAResInThree_of {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hSyl : KFactCaseTwoSylow) (hSch : KFactCatalogSchreier) (hAT : KFactCaseTwoAlphaThree) :
    D1CaseTwoNTwoAResInThree G := by
  intro P M H R Rbar hd hnosp hin
  intros
  exact D1CaseTwoData3.false_of_in_three hd hOut hS hSyl hSch hAT hnosp hin

theorem d1CaseTwoZZThreeIn_of {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hSyl : KFactCaseTwoSylow) (hSch : KFactCatalogSchreier) (hAT : KFactCaseTwoAlphaThree) :
    D1CaseTwoZZThreeIn G := by
  intro P M H R Rbar hd hnosp hin
  intros
  exact D1CaseTwoData3.false_of_in_three hd hOut hS hSyl hSch hAT hnosp hin

end CFSG.LocalAnalysis.RankThreeTheoremC
