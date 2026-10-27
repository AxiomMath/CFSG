module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34Lemma46FusionStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    ¬ IsThreeConnected (S ⊓ withKernel J) →
    Monoid.exponent ↥(S ⊓ zStarIn J) = 4 → ¬ IsCyclic ↥(S ⊓ zStarIn J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      L34ZConjClosed J S (normalizer (W : Set G)) →
      normalizer (S : Set G) ≤ normalizer (W : Set G) → (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
      ∀ b ∈ S, (∃ g : G, b = g⁻¹ * a * g) →
        3 ≤ pRank 2 ↥(S ⊓ J ⊓ centralizer ({b} : Set G)) →
        ∃ m ∈ normalizer (W : Set G), b = m⁻¹ * a * m

@[expose] def L34Lemma46FieldSquareStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    ¬ IsThreeConnected (S ⊓ withKernel J) →
    Monoid.exponent ↥(S ⊓ zStarIn J) = 4 → ¬ IsCyclic ↥(S ⊓ zStarIn J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      L34ZConjClosed J S (normalizer (W : Set G)) →
      normalizer (S : Set G) ≤ normalizer (W : Set G) → (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
      ∀ b ∈ S, (∃ g : G, b = g⁻¹ * a * g) → b ∉ zStarIn J →
        pRank 2 ↥(S ⊓ J ⊓ centralizer ({b} : Set G)) < 3 →
        ∃ z ∈ S ⊓ centralizer ({b} : Set G), z * z = a

@[expose] def L34Lemma46SquareRankStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    ¬ IsThreeConnected (S ⊓ withKernel J) →
    Monoid.exponent ↥(S ⊓ zStarIn J) = 4 → ¬ IsCyclic ↥(S ⊓ zStarIn J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      L34ZConjClosed J S (normalizer (W : Set G)) →
      normalizer (S : Set G) ≤ normalizer (W : Set G) → (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
      ∀ v ∈ S, (∃ g : G, v * v = g⁻¹ * a * g) →
        3 ≤ pRank 2 ↥(S ⊓ J ⊓ centralizer ({v * v} : Set G))

end CFSG.ComponentClassification.GrSLit
