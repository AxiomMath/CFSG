module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoSPDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CzShape (p : ℕ) (P : Sylow p G) (M R : Subgroup G) (z : G) : Prop :=
  (∀ m ∈ M, ∀ T : Sylow p (Subgroup.centralizer ({z} : Set G)),
    R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype →
    (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
      (P : Subgroup G).map (MulAut.conj m).toMonoidHom →
    ∃ t ∈ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype,
      (∀ g ∈ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype, Commute t g) ∧
      orderOf t = p ∧ t ∉ Subgroup.zpowers z ∧
      ∀ g ∈ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype,
        (∀ h ∈ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype,
          Commute g h) → g ^ p = 1 → g ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers z) ∧
  pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))

@[expose] def D1CaseTwoCand (p : ℕ) (M H R : Subgroup G) (z : H) : Prop :=
  ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
    ¬ L ≤ d1X0 p M H ∧ (z : G) ∈ R ∧ orderOf (z : G) = p ∧
    R ≤ Subgroup.centralizer ({(z : G)} : Set G) ∧
    QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))

@[expose] def D1CaseTwoAllOutEV (p : ℕ) (M H R : Subgroup G) : Prop :=
  ∀ z : H, D1CaseTwoCand p M H R z → D1CzOutside p (z : G) ∧ D1CzB0 p R (z : G) ∧
    pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ ∧ D1CzEven p (z : G)

end Defs

@[expose] def D1CaseTwoShape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzShape p P M R (z : G)

@[expose] def D1CaseTwoPosZeroEV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1CaseTwoNoSP p M H R → D1CaseTwoAllOutEV p M H R →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) → pCorePreimage p M ⊓ R = ⊥ → False

@[expose] def D1CaseTwoPosZeroIn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1CaseTwoNoSP p M H R →
    (∃ z : H, D1CaseTwoCand p M H R z ∧ ¬ D1CzOutside p (z : G)) →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) → pCorePreimage p M ⊓ R = ⊥ → False

@[expose] def D1CaseTwoPosZeroInThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData 3 P M H R Rbar →
    D1CaseTwoNoSP 3 M H R →
    (∃ z : H, D1CaseTwoCand 3 M H R z ∧ ¬ D1CzOutside 3 (z : G)) →
    D1UniqueOver H R (nclIn H (d1LayerX 3 H R)) → pCorePreimage 3 M ⊓ R = ⊥ → False

@[expose] def D1CaseTwoNTwoAResEV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1CaseTwoNoSP p M H R → D1CaseTwoAllOutEV p M H R →
    D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      d1LiftX p H R L₂ ≤
        nclIn M ⁅GLBPrimeCore p H, nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)⁆ →
      False

@[expose] def D1CaseTwoNTwoAResIn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1CaseTwoNoSP p M H R →
    (∃ z : H, D1CaseTwoCand p M H R z ∧ ¬ D1CzOutside p (z : G)) →
    D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      d1LiftX p H R L₂ ≤
        nclIn M ⁅GLBPrimeCore p H, nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)⁆ →
      False

@[expose] def D1CaseTwoNTwoAResInThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData 3 P M H R Rbar →
    D1CaseTwoNoSP 3 M H R →
    (∃ z : H, D1CaseTwoCand 3 M H R z ∧ ¬ D1CzOutside 3 (z : G)) →
    D1UniqueOver H R (nclIn H (pCorePreimage 3 M ⊓ d1LayerX 3 H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 3 M H → L₂ ≤ d1X0 3 M H →
      d1MapPCore 3 M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ L₁) ≠ ⊥ →
      d1LiftX 3 H R L₂ ≤
        nclIn M ⁅GLBPrimeCore 3 H, nclIn H (pCorePreimage 3 M ⊓ d1LayerX 3 H R)⁆ →
      False

@[expose] def D1CaseTwoZZThreeEV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData 3 P M H R Rbar →
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

@[expose] def D1CaseTwoZZThreeIn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData 3 P M H R Rbar →
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

@[expose] def KFactCaseTwoSylow : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K], IsCaseTwoGroup p K → ∀ T : Sylow p K,
    p ^ 2 ≤ Nat.card T

@[expose] def KFactCaseTwoNoTwo : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K], IsCaseTwoGroup p K → ∀ t : K, orderOf t = p →
    ∀ U : Subgroup (MulAut K), IsPGroup 2 U →
      MulAut.conj t ∈ Subgroup.normalizer (U : Set (MulAut K)) → U = ⊥

@[expose] def KFactCenterFive : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) → 5 ∣ Nat.card (Subgroup.center K) →
      4 ≤ Open.pRank 5 (⊤ : Subgroup K)

end CFSG.AGLEmbedding
