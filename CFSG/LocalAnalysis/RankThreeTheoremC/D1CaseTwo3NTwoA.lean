module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoA
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NTwoAClass
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NTwoAZN
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseTwoPosNTwoA' (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      False

@[expose] def D1CaseTwoNTwoARes (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      d1LiftX p H R L₂ ≤
        nclIn M ⁅GLBPrimeCore p H, nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)⁆ →
      False

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.inf_d1LayerX_ne_bot (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoData3 p P M H R Rbar) {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) ≠ ⊥) :
    pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥ :=
  D1CaseTwoDataAt.inf_d1LayerX_ne_bot (hAut := (kFactCycAut_of_kFactOutCyclic hOut)) (hS := hS)
    (hKL := hKL) (h84 := h84) (hD2 := hD2) (hd := hd.toAt) (hL := hL) (hmeet := hmeet)

theorem D1CaseTwoData3.false_of_unique_pCore (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hzz : D1CaseTwoZZ G) (hesc : D1CaseTwoEscaping G)
    (h2a' : D1CaseTwoPosNTwoA' G) (hd : D1CaseTwoData3 p P M H R Rbar)
    (hY : pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥)
    (huniq : D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R))) : False :=
  hd.toAt.false_of_unique_pCore (kFactCycAut_of_kFactOutCyclic hOut) hS hKL h84 hD2 hCGT hY huniq
    (hesc p P M H R Rbar hd) (h2a' p P M H R Rbar hd huniq)
    (fun huniq' => hzz p P M H R Rbar hd huniq')

end Data

theorem d1CaseTwoPosNTwoA_of_pCore {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hC : D1CaseTwoComp3 G) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock) (hzz : D1CaseTwoZZ G)
    (h2a' : D1CaseTwoPosNTwoA' G) : D1CaseTwoPosNTwoA G := by
  intro p P M H R Rbar hd _ L₁ L₂ hL₁ hL₂ hL₁X₀ hL₂X₀ hVL₁
  obtain ⟨H₀, Rbar₀, hd₀, hY₀, huniq₀⟩ := hd.exists_unique_pCore hOut hC hS hKL hInv hSch h84
    hD2 (hd.inf_d1LayerX_ne_bot hOut hS hKL h84 hD2 hL₁ hVL₁)
  exact hd₀.false_of_unique_pCore hOut hS hKL h84 hD2 hCGT hzz
    (d1CaseTwoEscaping_of hOut hS hKL h84 hD2) h2a' hY₀ huniq₀

theorem d1CaseTwoPosNTwoA'_of_res {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hres : D1CaseTwoNTwoARes G) : D1CaseTwoPosNTwoA' G := by
  intro p P M H R Rbar hd huniq L₁ L₂ hL₁ hL₂ hL₁X₀ hL₂X₀ hVL₁
  exact hres p P M H R Rbar hd huniq L₁ L₂ hL₁ hL₂ hL₁X₀ hL₂X₀ hVL₁
    (hd.d1LiftX_le_nclIn_of_unique hOut hS hKL h84 hCGT hD2 huniq hL₁ hL₂ hL₁X₀ hL₂X₀ hVL₁)

theorem d1CaseTwoPosNTwoA_of {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hC : D1CaseTwoComp3 G) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hCGT : AschbacherLocalCGTBlock) (hzz : D1CaseTwoZZ G)
    (hres : D1CaseTwoNTwoARes G) : D1CaseTwoPosNTwoA G :=
  d1CaseTwoPosNTwoA_of_pCore hOut hC hS hKL hInv hSch h84 hD2 hCGT hzz
    (d1CaseTwoPosNTwoA'_of_res hOut hS hKL h84 hD2 hCGT hres)

theorem d1CaseTwoRankThree_of_res {G : Type} [Group G] [Finite G] (hOut : KFactOutCyclic)
    (hC : D1CaseTwoComp3 G) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hInv : D1CaseTwoInv3 G) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (h0 : D1CaseTwoPosZero G) (hres : D1CaseTwoNTwoARes G) (hz3 : D1CaseTwoZZThree G) :
    D1CaseTwoRankThree G :=
  d1CaseTwoRankThree_of hOut hC hS hKL hInv hSch h84 h85 h86 h93 hD2 hCGT hKin hKP hC3 hK5 h0
    (d1CaseTwoPosNTwoA_of hOut hC hS hKL hInv hSch h84 hD2 hCGT
      (d1CaseTwoZZ_of_zzThree hOut hS hKL hSch h84 h85 h86 h93 hD2 hKin hKP hC3 hK5 hz3) hres)
    hz3

end CFSG.LocalAnalysis.RankThreeTheoremC
