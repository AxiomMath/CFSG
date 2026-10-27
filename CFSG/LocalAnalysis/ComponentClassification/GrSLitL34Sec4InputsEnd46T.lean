module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def L34Lemma46TwoStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    ¬ IsThreeConnected (S ⊓ withKernel J) →
    Monoid.exponent ↥(S ⊓ zStarIn J) = 4 → ¬ IsCyclic ↥(S ⊓ zStarIn J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      L34ZConjClosed J S (normalizer (W : Set G)) →
      normalizer (S : Set G) ≤ normalizer (W : Set G) → (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
      (∀ y ∈ S, (∃ g : G, y = g⁻¹ * a * g) → y ∈ zStarIn J) →
      ∀ b ∈ S, (∃ g : G, b = g⁻¹ * a * g) → b ≠ a →
        (∀ y ∈ S, (∃ g : G, y = g⁻¹ * a * g) → y = a ∨ y = b) →
        (∀ s ∈ S, s * b = b * s) → (∃ n ∈ normalizer (S : Set G), b = n⁻¹ * a * n) → False

end CFSG.ComponentClassification.GrSLit
