module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def Harris82Lemma54Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsTwoQuasisimple X → IsMTypeSchur 3 X →
    ∀ (τ : StatedLieTag) (n : ℕ), Blueprint.LieModel (X ⧸ Open.fusionZStar X) τ n 3 1 →
    ∀ t : X, orderOf t = 2 → t ∈ Open.fusionZStar X →
      ∃ u : X, orderOf u = 2 ∧ u ∉ Open.fusionZStar X ∧ ∃ J₁ J₂ : Subgroup X,
        IsSolvableTwoComponentIn J₁ (centralizer {u}) ∧ u ∈ J₁ ∧
        Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* SL(2, ZMod 3)) ∧
        ((IsTwoComponentIn J₂ (centralizer {u}) ∧ ∃ (τ' : StatedLieTag) (n' : ℕ),
            Blueprint.LieModel (↥J₂ ⧸ Open.fusionZStar ↥J₂) τ' n' 3 1) ∨
          (IsSolvableTwoComponentIn J₂ (centralizer {u}) ∧
            Nonempty (↥J₂ ⧸ pPrimeCore 2 ↥J₂ ≃* SL(2, ZMod 3)))) ∧
        J₁ ≠ J₂ ∧ (t ∈ J₂ ∨ t * u ∈ J₂)

@[expose] def Harris82FourGroupThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ z₁ z₂ : G, orderOf z₁ = 2 → orderOf z₂ = 2 → z₁ ≠ z₂ → z₁ * z₂ = z₂ * z₁ →
    ∀ L₁ L₂ : Subgroup G, IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) →
    (IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) ∨
      IsSolvableTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂})) →
    z₁ ∈ L₁ → z₂ ∈ L₂ → Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)) →
    InductionType 3 ↥L₂ →
      ∃ K : Subgroup G, IsTwoComponentIn K (centralizer {z₁}) ∧
        GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K ∧ GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K ∧
        centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) ∧
        IsSimpleChevalleyOver 3 (↥K ⧸ Open.fusionZStar ↥K) ∧
        ∃ hz₂K : z₂ ∈ K, (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
          center (↥K ⧸ pPrimeCore 2 ↥K)

@[expose] def Harris82Lemma58bThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z₁ z₂ : G), orderOf z₁ = 2 → orderOf z₂ = 2 → z₁ ≠ z₂ →
    z₁ * z₂ = z₂ * z₁ → ∀ L₁ L₂ K : Subgroup G,
    IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) →
    (IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) ∨
      IsSolvableTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂})) →
    z₁ ∈ L₁ → z₂ ∈ L₂ → Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)) →
    IsTwoComponentIn K (centralizer {z₁}) → GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K →
    GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K →
    centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) →
    ∀ hz₂K : z₂ ∈ K, (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
      center (↥K ⧸ pPrimeCore 2 ↥K) →
    IsSimpleChevalleyOver 3 (↥K ⧸ Open.fusionZStar ↥K) →
      IsMTypeSchur 3 ↥K ∧
      ((IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) ∧
          ∃ (τ : StatedLieTag) (n : ℕ),
            Blueprint.LieModel (↥L₂ ⧸ Open.fusionZStar ↥L₂) τ n 3 1) →
        ∃ m : ℕ, Odd m ∧ 5 ≤ m ∧ IsCoverOf .POmegaOdd m 3 1 2 (↥K ⧸ pPrimeCore 2 ↥K)) ∧
      (Nonempty (↥L₂ ⧸ pPrimeCore 2 ↥L₂ ≃* SL(2, ZMod 3)) →
        IsCoverOf .POmegaOdd 3 3 1 2 (↥K ⧸ pPrimeCore 2 ↥K)) ∧
      ∀ r : ℕ, ¬ IsCoverOf .POmegaOdd 3 3 r 2 (↥L₂ ⧸ pPrimeCore 2 ↥L₂)

@[expose] def Lemma412ConclThree (X : Type) [Group X] : Prop :=
  ∃ z : X, orderOf z = 2 ∧ center X = zpowers z ∧
    ∃ (t : X) (J₁ J₂ : Subgroup X), orderOf t = 2 ∧ t ∉ center X ∧
      IsSolvableTwoComponentIn J₁ (centralizer {t}) ∧
      IsSolvableTwoComponentIn J₂ (centralizer {t}) ∧
      Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* SL(2, ZMod 3)) ∧
      Nonempty (↥J₂ ⧸ pPrimeCore 2 ↥J₂ ≃* SL(2, ZMod 3)) ∧
      (center ↥J₁).map J₁.subtype = zpowers t ∧ (center ↥J₂).map J₂.subtype = zpowers (t * z)

@[expose] def Harris82Lemma412Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m : ℕ), 4 ≤ m → IsCoverOf .POmegaOdd m 3 1 2 X →
    Lemma412ConclThree X

@[expose] def Aschbacher75Theorem2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (z : X), orderOf z = 2 → ∀ L : Subgroup X,
    IsTwoComponentIn L ⊤ →
    (∀ K : Subgroup X, IsSolvableTwoComponentIn K (centralizer {z}) →
      K ≤ normalizer (L : Set X) → z ∈ normalizer (L : Set X) →
      GH74.GLS.oPrimeResidualOf 2 K ≤ L ∨
        ⁅L, GH74.GLS.oPrimeResidualOf 2 K⁆ ≤ pPrimeCore 2 X) ∧
    ∀ K : Subgroup X, (IsTwoComponentIn K (centralizer {z}) ∨
        IsSolvableTwoComponentIn K (centralizer {z})) → z ∈ K →
      ⁅K, L⁆ ≤ pPrimeCore 2 X ∨ GH74.GLS.oPrimeResidualOf 2 K ≤ L

@[expose] def IsThetaBalanced (K : Type) [Group K] : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Nonempty (↥(Open.genFittingFStar H) ≃* K) →
    ∀ t : H, orderOf t = 2 →
      Nat.Coprime (Nat.card ↥(pPrimeCore 2 ↥(centralizer ({t} : Set H)))) 3

@[expose] def Harris82ThetaBalanceThree : Prop :=
  (∀ (K : Type) [Group K] [Finite K],
      ((IsSimpleChevalleyOver 3 K ∧ ∀ f : ℕ, ¬ Blueprint.LieModel K .PSL 2 3 f) ∨
        Nonempty (K ≃* ↥Blueprint.NativeSporadic.M11)) → IsThetaBalanced K) ∧
    ∀ (X : Type) [Group X] [Finite X],
      (∃ (τ : StatedLieTag) (n : ℕ), Blueprint.LieModel X τ n 3 1) →
      ∀ t : X, orderOf t = 2 → pPrimeCore 2 ↥(centralizer ({t} : Set X)) = ⊥

end CFSG.ComponentClassification.HarrisLit.T1
