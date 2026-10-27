module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34ZConjClosed {X : Type} [Group X] (J S M : Subgroup X) : Prop :=
  ∀ c ∈ S ⊓ zStarIn J, c * c = 1 → ∀ m ∈ M, m⁻¹ * c * m ∈ S → m⁻¹ * c * m ∈ zStarIn J

@[expose] def L34HeldCenterFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M K J : Subgroup G) (a : G), K ≤ M →
    IsPComponent 2 (K.subgroupOf M) →
    Nonempty (K ⧸ pPrimeCore 2 K ≃* Blueprint.NativeSporadic.He) → a ∈ M → orderOf a = 2 →
    J ≤ M ⊓ centralizer ({a} : Set G) →
    IsPComponent 2 (J.subgroupOf (M ⊓ centralizer ({a} : Set G))) →
    IsL34Type (J ⧸ Open.fusionZStar J) → J ≤ K ⊔ oddIn M → ∀ u ∈ zStarIn J, u * u ∈ oddIn J

@[expose] def L34Lemma46CenterStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    ¬ IsThreeConnected (S ⊓ withKernel J) →
    Monoid.exponent ↥(S ⊓ zStarIn J) = 4 → ¬ IsCyclic ↥(S ⊓ zStarIn J) →
    ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → ∀ j ∈ J, j⁻¹ * s⁻¹ * j * s ∈ zStarIn J

@[expose] def L34Lemma46ClosedStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    ¬ IsThreeConnected (S ⊓ withKernel J) →
    Monoid.exponent ↥(S ⊓ zStarIn J) = 4 → ¬ IsCyclic ↥(S ⊓ zStarIn J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      L34ZConjClosed J S (normalizer (W : Set G)) →
      normalizer (S : Set G) ≤ normalizer (W : Set G) → (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
      ∃ B : Subgroup G, B ≤ S ⊓ zStarIn J ∧ B ≠ ⊥ ∧
        ∀ y ∈ B, ∀ g : G, g⁻¹ * y * g ∈ S → g⁻¹ * y * g ∈ B

end CFSG.ComponentClassification.GrSLit
