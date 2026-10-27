module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoA

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseTwoPosZeroNoSP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1CaseTwoNoSP p M H R →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) → pCorePreimage p M ⊓ R = ⊥ → False

@[expose] def D1CaseTwoNTwoAResNoSP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1CaseTwoNoSP p M H R →
    D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      d1LiftX p H R L₂ ≤
        nclIn M ⁅GLBPrimeCore p H, nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)⁆ →
      False

@[expose] def D1CaseTwoZZThreeNoSP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData 3 P M H R Rbar →
    D1CaseTwoNoSP 3 M H R →
    D1UniqueOver H R (nclIn H (d1LayerX 3 H R)) →
    ∀ L₁ : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L₁ ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = L₁) →
      d1MapPCore 3 M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ L₁) ≠ ⊥ →
      d1MapPCore 3 M H ⊓ CFSG.pCore 3 (H ⧸ primeComplementCore (G := H) 3) = ⊥ →
      ¬ IsPGroup 3 (Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) 3))) →
      ∀ z : H, (z : G) ∈ R → orderOf z = 3 →
        QuotientGroup.mk' (primeComplementCore (G := H) 3) z ∈
          CFSG.pCore 3 (H ⧸ primeComplementCore (G := H) 3) →
        (z : G) ∈ nclIn M ⁅GLBPrimeCore 3 H, nclIn H (d1LayerX 3 H R)⁆ → False

theorem d1CaseTwoPosZero_of_noSP (hSP : D1CaseTwoSP) (h : D1CaseTwoPosZeroNoSP) :
    D1CaseTwoPosZero := fun G _ _ p P M H R Rbar hd =>
  h G p P M H R Rbar hd (hSP G p P M H R Rbar hd)

theorem d1CaseTwoNTwoARes_of_noSP (hSP : D1CaseTwoSP) (h : D1CaseTwoNTwoAResNoSP) :
    D1CaseTwoNTwoARes := fun G _ _ p P M H R Rbar hd =>
  h G p P M H R Rbar hd (hSP G p P M H R Rbar hd)

theorem d1CaseTwoZZThree_of_noSP (hSP : D1CaseTwoSP) (h : D1CaseTwoZZThreeNoSP) :
    D1CaseTwoZZThree := fun G _ _ P M H R Rbar hd =>
  h G P M H R Rbar hd (hSP G 3 P M H R Rbar hd)

end CFSG.AGLEmbedding
