module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseTwoShape (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzShape p P M R (z : G)

@[expose] def D1CaseTwoPosZeroEV (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    D1CaseTwoNoSP p M H R → D1CaseTwoAllOutEV p M H R →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) → pCorePreimage p M ⊓ R = ⊥ → False

@[expose] def D1CaseTwoPosZeroIn (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    D1CaseTwoNoSP p M H R →
    (∃ z : H, D1CaseTwoCand p M H R z ∧ ¬ D1CzOutside p (z : G)) →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) → pCorePreimage p M ⊓ R = ⊥ → False

@[expose] def D1CaseTwoPosZeroInThree (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData3 3 P M H R Rbar →
    D1CaseTwoNoSP 3 M H R →
    (∃ z : H, D1CaseTwoCand 3 M H R z ∧ ¬ D1CzOutside 3 (z : G)) →
    D1UniqueOver H R (nclIn H (d1LayerX 3 H R)) → pCorePreimage 3 M ⊓ R = ⊥ → False

@[expose] def D1CaseTwoNTwoAResEV (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    D1CaseTwoNoSP p M H R → D1CaseTwoAllOutEV p M H R →
    D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      d1LiftX p H R L₂ ≤
        nclIn M ⁅GLBPrimeCore p H, nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)⁆ →
      False

@[expose] def D1CaseTwoNTwoAResIn (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    D1CaseTwoNoSP p M H R →
    (∃ z : H, D1CaseTwoCand p M H R z ∧ ¬ D1CzOutside p (z : G)) →
    D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      d1LiftX p H R L₂ ≤
        nclIn M ⁅GLBPrimeCore p H, nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)⁆ →
      False

@[expose] def D1CaseTwoNTwoAResInThree (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData3 3 P M H R Rbar →
    D1CaseTwoNoSP 3 M H R →
    (∃ z : H, D1CaseTwoCand 3 M H R z ∧ ¬ D1CzOutside 3 (z : G)) →
    D1UniqueOver H R (nclIn H (pCorePreimage 3 M ⊓ d1LayerX 3 H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 3 M H → L₂ ≤ d1X0 3 M H →
      d1MapPCore 3 M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ L₁) ≠ ⊥ →
      d1LiftX 3 H R L₂ ≤
        nclIn M ⁅GLBPrimeCore 3 H, nclIn H (pCorePreimage 3 M ⊓ d1LayerX 3 H R)⁆ →
      False

@[expose] def D1CaseTwoZZThreeEV (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData3 3 P M H R Rbar →
    D1CaseTwoNoSP 3 M H R → D1CaseTwoAllOutEV 3 M H R →
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

@[expose] def D1CaseTwoZZThreeIn (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData3 3 P M H R Rbar →
    D1CaseTwoNoSP 3 M H R →
    (∃ z : H, D1CaseTwoCand 3 M H R z ∧ ¬ D1CzOutside 3 (z : G)) →
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

end CFSG.LocalAnalysis.RankThreeTheoremC
