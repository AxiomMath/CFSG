module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoAssembly
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAClass
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAZN
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoZZFive
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseTwoPosNTwoA' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      False

@[expose] def D1CaseTwoNTwoARes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
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

theorem D1CaseTwoDataAt.inf_d1LayerX_ne_bot (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoDataAt p P M H R Rbar) {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) ≠ ⊥) :
    pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥ := by
  have h3 := hd.toPhaseThree hAut hS hKL
  have : Fact p.Prime := ⟨h3.prime⟩
  obtain ⟨t, ⟨htV, -, htL⟩, htp, -⟩ := exists_mem_centralizer_orderOf_eq
    (Rbar.isPGroup'.to_le (inf_le_right.trans inf_le_left)) hmeet
  rw [h3.d1MapPCore_eq h84 hD2] at htV
  obtain ⟨r, ⟨hrR, hrY⟩, rfl⟩ := htV
  intro hbot
  have hr : (r : G) ∈ pCorePreimage p M ⊓ d1LayerX p H R :=
    ⟨hrY, r, ⟨hrR, le_layer_of_isComponentOf hL htL⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hr
  rw [show r = 1 from Subtype.ext hr, map_one, orderOf_one] at htp
  exact h3.prime.one_lt.ne htp

theorem D1CaseTwoData.inf_d1LayerX_ne_bot (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoData p P M H R Rbar) {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) ≠ ⊥) :
    pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥ :=
  D1CaseTwoDataAt.inf_d1LayerX_ne_bot (hAut := (kFactCycAut_of_kFactBeta hβ)) (hS := hS)
    (hKL := hKL) (h84 := h84) (hD2 := hD2) (hd := hd.toAt) (hL := hL) (hmeet := hmeet)

theorem D1CaseTwoDataAt.false_of_unique_pCore (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hd : D1CaseTwoDataAt p P M H R Rbar)
    (hY : pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥)
    (huniq : D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)))
    (hesc : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      ¬ L ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥ →
      pCorePreimage p M ⊓ R ≠ ⊥ → False)
    (h2a' : ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      False)
    (hzz : D1UniqueOver H R (nclIn H (d1LayerX p H R)) →
      ∀ L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
        (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁) →
        d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
        d1MapPCore p M H ⊓ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ →
        ¬ IsPGroup p (Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) p))) →
        ∀ z : H, (z : G) ∈ R → orderOf z = p →
          QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
            CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) →
          (z : G) ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆ → False) : False := by
  have hV : pCorePreimage p M ⊓ R ≠ ⊥ := fun hbot => hY (le_bot_iff.mp
    (hbot ▸ le_inf inf_le_left (inf_le_right.trans (d1LiftX_le p H R _))))
  by_cases he : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥
  · obtain ⟨L, hL, hLX₀, hVL⟩ := he
    exact hesc L hL hLX₀ hVL hV
  push Not at he
  by_cases h2 : ∃ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₂ ⊤ ∧
      L₂ ≤ d1X0 p M H
  · obtain ⟨L₂, hL₂, hL₂X₀⟩ := h2
    obtain ⟨L₁, hL₁, hL₁X₀⟩ := hd.exists_not_le hAut
    exact h2a' L₁ L₂ hL₁ hL₂ hL₁X₀ hL₂X₀ (he L₁ hL₁ hL₁X₀)
  push Not at h2
  have hJ : nclIn H (pCorePreimage p M ⊓ d1LayerX p H R) ≤ nclIn H (d1LayerX p H R) :=
    nclIn_le (inf_le_right.trans (le_nclIn (d1LiftX_le_H p H R _))) (nclIn_le_self H _)
      (le_normalizer_nclIn H _)
  have huniq' : D1UniqueOver H R (nclIn H (d1LayerX p H R)) :=
    fun H' hH' hJH' hRH' => huniq H' hH' (hJ.trans hJH') hRH'
  exact hd.false_of_forall_not_le hAut hS hKL h84 hD2 hCGT huniq' h2 (fun L hL => he L hL (h2 L hL))
    (hzz huniq')

theorem D1CaseTwoData.false_of_unique_pCore (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hzz : D1CaseTwoZZ) (hesc : D1CaseTwoEscaping)
    (h2a' : D1CaseTwoPosNTwoA') (hd : D1CaseTwoData p P M H R Rbar)
    (hY : pCorePreimage p M ⊓ d1LayerX p H R ≠ ⊥)
    (huniq : D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R))) : False :=
  hd.toAt.false_of_unique_pCore (kFactCycAut_of_kFactBeta hβ) hS hKL h84 hD2 hCGT hY huniq
    (hesc G p P M H R Rbar hd) (h2a' G p P M H R Rbar hd huniq)
    (fun huniq' => hzz G p P M H R Rbar hd huniq')

end Data

theorem d1CaseTwoPosNTwoA_of_pCore (hβ : KFactBeta) (hα : KFactAlphaW) (h3 : D1CaseThree)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hzz : D1CaseTwoZZ) (hesc : D1CaseTwoEscaping)
    (h2a' : D1CaseTwoPosNTwoA') : D1CaseTwoPosNTwoA := by
  intro G _ _ p P M H R Rbar hd _ L₁ L₂ hL₁ hL₂ hL₁X₀ hL₂X₀ hVL₁
  obtain ⟨H₀, Rbar₀, hd₀, hY₀, huniq₀⟩ := hd.exists_unique_pCore hβ hα h3 hS hKL hInv hSch h84
    hD2 (hd.inf_d1LayerX_ne_bot hβ hS hKL h84 hD2 hL₁ hVL₁)
  exact hd₀.false_of_unique_pCore hβ hS hKL h84 hD2 hCGT hzz hesc h2a' hY₀ huniq₀

theorem d1CaseTwoPosNTwoA'_of_res (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hres : D1CaseTwoNTwoARes) : D1CaseTwoPosNTwoA' := by
  intro G _ _ p P M H R Rbar hd huniq L₁ L₂ hL₁ hL₂ hL₁X₀ hL₂X₀ hVL₁
  exact hres G p P M H R Rbar hd huniq L₁ L₂ hL₁ hL₂ hL₁X₀ hL₂X₀ hVL₁
    (hd.d1LiftX_le_nclIn_of_unique hβ hS hKL h84 hCGT hD2 huniq hL₁ hL₂ hL₁X₀ hL₂X₀ hVL₁)

theorem d1CaseTwoPosNTwoA_of (hβ : KFactBeta) (hα : KFactAlphaW) (h3 : D1CaseThree)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hzz : D1CaseTwoZZ) (hesc : D1CaseTwoEscaping)
    (hres : D1CaseTwoNTwoARes) : D1CaseTwoPosNTwoA :=
  d1CaseTwoPosNTwoA_of_pCore hβ hα h3 hS hKL hInv hSch h84 hD2 hCGT hzz hesc
    (d1CaseTwoPosNTwoA'_of_res hβ hS hKL h84 hD2 hCGT hres)

theorem d1CaseTwoRankThree_of_res (hβ : KFactBeta) (hα : KFactAlphaW) (h3 : D1CaseThree)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (h0 : D1CaseTwoPosZero) (hres : D1CaseTwoNTwoARes) (hz3 : D1CaseTwoZZThree)
    (hesc : D1CaseTwoEscaping) : D1CaseTwoRankThree :=
  d1CaseTwoRankThree_of hβ hα h3 hS hKL hInv hSch h84 h85 h86 h93 hD2 hCGT hKin hKP hC3 hK5 h0
    (d1CaseTwoPosNTwoA_of hβ hα h3 hS hKL hInv hSch h84 hD2 hCGT
      (d1CaseTwoZZ_of_zzThree hβ hS hKL hSch h84 h85 h86 h93 hD2 hKin hKP hC3 hK5 hz3) hesc hres)
    hz3 hesc

end CFSG.AGLEmbedding
