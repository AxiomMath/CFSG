module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarNF
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NoSPDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3StarData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseTwoNormalForm (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
      D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) →
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
        (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H → False

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.false_of_nf (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo)
    (hKO : LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner) (hC : D1CaseTwoComp3 G)
    (hNF : D1CaseTwoNormalForm G) (hd : D1CaseTwoData3 p P M H R Rbar)
    (hnosp : D1CaseTwoNoSP p M H R) (hEV : D1CaseTwoAllOutEV p M H R) : False :=
  hd.toAt.false_of_nf_of (kFactCycAut_of_kFactOutCyclic hOut) hS hL2 hInv.toIn hSch hSyl hNo2
    hnosp hEV fun z hz hnSP hout hB0 hQ hEven hKax Hs hHs hLHs => by
      obtain ⟨Rbars, hds, hzHs, hzs⟩ := D1CaseTwoData3.caseTwoData_star hOut hS hInv hSch hSyl
        hKO hC hd hz hnSP hout hB0 hHs hLHs
      exact hNF p P M Hs R Rbars hds ⟨z, hzHs⟩ hzs hnSP hout hB0 hQ hEven hKax hLHs

section Residues

variable (hOut : KFactOutCyclic) (hS : KFactSeitzCyc) (hL2 : KFactCaseTwoLocal)
  (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier) (hSyl : KFactCaseTwoSylow)
  (hNo2 : KFactCaseTwoNoTwo) (hKO : LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner)
  (hC : D1CaseTwoComp3 G) (hNF : D1CaseTwoNormalForm G)

include hOut hS hL2 hInv hSch hSyl hNo2 hKO hC hNF

theorem d1CaseTwoPosZeroEV_of_nf : D1CaseTwoPosZeroEV G := by
  intro p P M H R Rbar hd hnosp hEV _ _
  exact D1CaseTwoData3.false_of_nf hOut hS hL2 hInv hSch hSyl hNo2 hKO hC hNF hd hnosp hEV

theorem d1CaseTwoNTwoAResEV_of_nf : D1CaseTwoNTwoAResEV G := by
  intro p P M H R Rbar hd hnosp hEV _ _ _ _ _ _ _ _ _
  exact D1CaseTwoData3.false_of_nf hOut hS hL2 hInv hSch hSyl hNo2 hKO hC hNF hd hnosp hEV

theorem d1CaseTwoZZThreeEV_of_nf : D1CaseTwoZZThreeEV G := by
  intro P M H R Rbar hd hnosp hEV _ _ _ _ _ _ _ _ _ _ _ _
  exact D1CaseTwoData3.false_of_nf hOut hS hL2 hInv hSch hSyl hNo2 hKO hC hNF hd hnosp hEV

end Residues

end CFSG.LocalAnalysis.RankThreeTheoremC
