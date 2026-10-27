module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAZN
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.d1LiftX_le_nclIn_of_unique (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) (hd : D1CaseTwoData3 p P M H R Rbar)
    (huniq : D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)))
    {L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₁ : IsComponentOf L₁ ⊤)
    (hL₂ : IsComponentOf L₂ ⊤) (hL₁X₀ : ¬ L₁ ≤ d1X0 p M H) (hL₂X₀ : L₂ ≤ d1X0 p M H)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥) :
    d1LiftX p H R L₂ ≤
      nclIn M ⁅GLBPrimeCore p H, nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)⁆ :=
  D1CaseTwoDataAt.d1LiftX_le_nclIn_of_unique (hAut := (kFactCycAut_of_kFactOutCyclic hOut))
    (hS := hS) (hKL := hKL) (h84 := h84) (hCGT := hCGT) (hD2 := hD2) (hd := hd.toAt)
    (huniq := huniq) (hL₁ := hL₁) (hL₂ := hL₂) (hL₁X₀ := hL₁X₀) (hL₂X₀ := hL₂X₀) (hmeet := hmeet)

end Data

end CFSG.LocalAnalysis.RankThreeTheoremC
