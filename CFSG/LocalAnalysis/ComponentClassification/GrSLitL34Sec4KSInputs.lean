module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34Lemma43KSylowStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsThreeConnected (S ⊓ withKernel J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        IsL34Type (K ⧸ Open.fusionZStar K) →
        (J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) ∨
          (conjugate K a ≠ K ∧ J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G)))) →
        normalizer (W : Set G) ≤ normalizer (K : Set G) ∧
          IsSylowTwoIn S (normalizer (W : Set G))

@[expose] def L34Lemma46FrattiniStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    ¬ IsThreeConnected (S ⊓ withKernel J) →
    Monoid.exponent ↥(S ⊓ zStarIn J) = 4 → ¬ IsCyclic ↥(S ⊓ zStarIn J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        IsL34Type (K ⧸ Open.fusionZStar K) →
        J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) →
        normalizer (W : Set G) ≤ oddIn (normalizer (W : Set G)) ⊔ normalizer (J : Set G)

@[expose] def L34KSylowStep : Prop := L34Lemma43KSylowStep ∧ L34Lemma46FrattiniStep

@[expose] def L34Lemma43SylowStepKS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → L34Sec4Running J A → IsThreeConnected (S ⊓ withKernel J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) →
        normalizer (W : Set G) ≤ normalizer (K : Set G) →
        IsSylowTwoIn S (normalizer (W : Set G)) →
        ∃ P : Sylow 2 G, (P : Subgroup G) = S

@[expose] def L34Lemma43FusionStepKS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → L34Sec4Running J A → IsThreeConnected (S ⊓ withKernel J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) →
        normalizer (W : Set G) ≤ normalizer (K : Set G) →
        IsSylowTwoIn S (normalizer (W : Set G)) →
        (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
        ∀ g : G, g⁻¹ * a * g ∈ normalizer (W : Set G) →
          ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m

end CFSG.ComponentClassification.GrSLit

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34Lemma43BadFusionStepKS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → L34Sec4Running J A → IsThreeConnected (S ⊓ withKernel J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) →
        normalizer (W : Set G) ≤ normalizer (K : Set G) →
        IsSylowTwoIn S (normalizer (W : Set G)) →
        (∃ P : Sylow 2 G, (P : Subgroup G) = S) →
        ∀ g : G, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∉ withKernel J →
          (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) →
          ((IsCyclic ↥(S ⊓ zStarIn J) ∧ Nat.card ↥(S ⊓ zStarIn J) ≤ 4 ∧
              IsL34Unitary J (g⁻¹ * a * g)) ∨
            (Nat.card ↥(S ⊓ zStarIn J) = 16 ∧ HarrisLit.EndB.IsL34Field J (g⁻¹ * a * g))) →
          ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m

end CFSG.ComponentClassification.GrSLit.GrS5S
