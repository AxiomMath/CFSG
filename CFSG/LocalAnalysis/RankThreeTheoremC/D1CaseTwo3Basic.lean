module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseTwoClass (p : ℕ) (P : Sylow p G) (M R X H : Subgroup G) : Prop :=
  ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
    D1CaseTwoData3 p P M H R Rbar ∧ d1LayerX p H R = X

end Defs

@[expose] def D1CaseTwoPosZero (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) → pCorePreimage p M ⊓ R = ⊥ → False

@[expose] def D1CaseTwoPosNTwoA (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      False

@[expose] def D1CaseTwoZZ (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) →
    ∀ L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁) →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      d1MapPCore p M H ⊓ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ →
      ¬ IsPGroup p (Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) p))) →
      ∀ z : H, (z : G) ∈ R → orderOf z = p →
        QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
          CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) →
        (z : G) ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆ → False

@[expose] def D1CaseTwoZZThree (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData3 3 P M H R Rbar →
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

@[expose] def D1CaseTwoUnique (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData3 p P M H R Rbar →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) → False

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.exists_not_le (hOut : KFactOutCyclic) (hd : D1CaseTwoData3 p P M H R Rbar) :
    ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H :=
  hd.toAt.exists_not_le (kFactCycAut_of_kFactOutCyclic hOut)

end Data

end CFSG.LocalAnalysis.RankThreeTheoremC
