module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSP
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NoSPBZero
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NoSPShape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R : Subgroup G}
  {Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5)}

theorem D1CaseTwoData3.false_of_in_five (hd : D1CaseTwoData3 5 P M H R Rbar) (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hSyl : KFactCaseTwoSylow) (hZ5 : KFactCenterFive)
    (hnosp : D1CaseTwoNoSP 5 M H R)
    (hin : ∃ z : H, D1CaseTwoCand 5 M H R z ∧ ¬ D1CzOutside 5 (z : G)) : False :=
  D1CaseTwoDataAt.false_of_in_five (hd := hd.toAt) (hAut := (kFactCycAut_of_kFactOutCyclic hOut))
    (hS := hS) (hSyl := hSyl) (hZ5 := hZ5) (hnosp := hnosp) (hin := hin)

end Data

theorem D1CaseTwoData3.three_or_five {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hd : D1CaseTwoData3 p P M H R Rbar) (hOut : KFactOutCyclic) (hS : KFactSeitzCyc) {z : H}
    (hz : D1CaseTwoCand p M H R z) : p = 3 ∨ p = 5 :=
  D1CaseTwoDataAt.three_or_five (hd := hd.toAt) (hAut := (kFactCycAut_of_kFactOutCyclic hOut))
    (hS := hS) (hz := hz)

theorem d1CaseTwoPosZeroIn_of {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hSyl : KFactCaseTwoSylow) (hZ5 : KFactCenterFive) (h3 : D1CaseTwoPosZeroInThree G) :
    D1CaseTwoPosZeroIn G := by
  intro p P M H R Rbar hd hnosp hin hU h0
  obtain ⟨z, hz, -⟩ := id hin
  rcases D1CaseTwoData3.three_or_five hd hOut hS hz with rfl | rfl
  · exact h3 P M H R Rbar hd hnosp hin hU h0
  · exact D1CaseTwoData3.false_of_in_five hd hOut hS hSyl hZ5 hnosp hin

theorem d1CaseTwoNTwoAResIn_of {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hSyl : KFactCaseTwoSylow) (hZ5 : KFactCenterFive) (h3 : D1CaseTwoNTwoAResInThree G) :
    D1CaseTwoNTwoAResIn G := by
  intro p P M H R Rbar hd hnosp hin hU L₁ L₂ h1 h2 h3' h4 h5 h6
  obtain ⟨z, hz, -⟩ := id hin
  rcases D1CaseTwoData3.three_or_five hd hOut hS hz with rfl | rfl
  · exact h3 P M H R Rbar hd hnosp hin hU L₁ L₂ h1 h2 h3' h4 h5 h6
  · exact D1CaseTwoData3.false_of_in_five hd hOut hS hSyl hZ5 hnosp hin

theorem d1CaseTwoPosZeroNoSP_of_kFacts {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hEV : D1CaseTwoPosZeroEV G)
    (hIn : D1CaseTwoPosZeroIn G) : D1CaseTwoPosZeroNoSP G :=
  d1CaseTwoPosZeroNoSP_of (d1CaseTwoShape_of hOut hS hL2 hInv hSch hSyl hNo2) hEV hIn

theorem d1CaseTwoNTwoAResNoSP_of_kFacts {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hEV : D1CaseTwoNTwoAResEV G)
    (hIn : D1CaseTwoNTwoAResIn G) : D1CaseTwoNTwoAResNoSP G :=
  d1CaseTwoNTwoAResNoSP_of (d1CaseTwoShape_of hOut hS hL2 hInv hSch hSyl hNo2) hEV hIn

theorem d1CaseTwoZZThreeNoSP_of_kFacts {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hEV : D1CaseTwoZZThreeEV G)
    (hIn : D1CaseTwoZZThreeIn G) : D1CaseTwoZZThreeNoSP G :=
  d1CaseTwoZZThreeNoSP_of (d1CaseTwoShape_of hOut hS hL2 hInv hSch hSyl hNo2) hEV hIn

theorem d1CaseTwoPosZeroNoSP_of_residues {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hZ5 : KFactCenterFive)
    (hEV : D1CaseTwoPosZeroEV G) (hIn : D1CaseTwoPosZeroInThree G) : D1CaseTwoPosZeroNoSP G :=
  d1CaseTwoPosZeroNoSP_of_kFacts hOut hS hL2 hInv hSch hSyl hNo2 hEV
    (d1CaseTwoPosZeroIn_of hOut hS hSyl hZ5 hIn)

theorem d1CaseTwoNTwoAResNoSP_of_residues {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hZ5 : KFactCenterFive)
    (hEV : D1CaseTwoNTwoAResEV G) (hIn : D1CaseTwoNTwoAResInThree G) : D1CaseTwoNTwoAResNoSP G :=
  d1CaseTwoNTwoAResNoSP_of_kFacts hOut hS hL2 hInv hSch hSyl hNo2 hEV
    (d1CaseTwoNTwoAResIn_of hOut hS hSyl hZ5 hIn)

end CFSG.LocalAnalysis.RankThreeTheoremC
