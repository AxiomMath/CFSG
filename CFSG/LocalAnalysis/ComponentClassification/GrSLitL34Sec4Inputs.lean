module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

@[expose] def IsL34Unitary {G : Type*} [Group G] (J : Subgroup G) (x : G) : Prop :=
  x ∈ normalizer (J : Set G) ∧ x * x = 1 ∧ x ∉ withKernel J ∧
    Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} = 72 * Nat.card (zStarIn J)

@[expose] def L34UnbalancingUnitaryStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J : Subgroup G), GSUnbalancingTriple a x J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsL34Unitary J x

@[expose] def L34UnitaryCentralizerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G) (x : G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsL34Unitary J x → IsSylowTwoIn P J →
    x ∈ normalizer (P : Set G) →
    (∀ z ∈ P ⊓ zStarIn J, x⁻¹ * z * x = z⁻¹) ∧
    Nat.card ↥(P ⊓ centralizer ({x} : Set G)) = 8 ∧
    Nat.card ↥(J ⊓ centralizer ({x} : Set G)) =
      72 * Nat.card ↥(oddIn J ⊓ centralizer ({x} : Set G)) ∧
    (P ⊓ zStarIn J = ⊥ →
      Nonempty (↥(P ⊓ centralizer ({x} : Set G)) ≃* QuaternionGroup 2)) ∧
    (P ⊓ zStarIn J ≠ ⊥ → IsCyclic ↥(P ⊓ zStarIn J) →
      (∀ u ∈ P ⊓ centralizer ({x} : Set G), ∀ v ∈ P ⊓ centralizer ({x} : Set G),
        u * v = v * u) ∧
      Monoid.exponent ↥(P ⊓ centralizer ({x} : Set G)) = 4) ∧
    (¬ IsCyclic ↥(P ⊓ zStarIn J) → IsElemTwo (P ⊓ centralizer ({x} : Set G))) ∧
    (∃ Y : Subgroup G, Y ≤ P ⊓ centralizer ({x} : Set G) ∧
      P ⊓ zStarIn J ⊓ centralizer ({x} : Set G) ⊓ Y = ⊥ ∧
      P ⊓ zStarIn J ⊓ centralizer ({x} : Set G) ⊔ Y = P ⊓ centralizer ({x} : Set G)) ∧
    ∀ p ∈ P, p * x * (p * x) = 1 → ∃ q ∈ P, p * x = q⁻¹ * x * q

@[expose] def L34BorelGenerationFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P C : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J → ¬ IsCyclic ↥(P ⊓ zStarIn J) →
    C ≤ P → IsElemTwo C → Nat.card C = 16 →
    (∀ y ∈ P, (∀ w ∈ P, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔ y ∈ C ⊔ (P ⊓ zStarIn J)) →
    J ⊓ normalizer (P : Set G) ≤
      oddIn J ⊔ ⨆ (E : Subgroup G) (_ : E ≤ C) (_ : IsEightGroup E), J ⊓ normalizer (E : Set G)

@[expose] def L34ParabolicFact : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsL34Type K → ∀ (T : Sylow 2 K) (X : Subgroup K),
    normalizer ((T : Subgroup K) : Set K) ≤ X → 9 ∣ Nat.card X → X = ⊤

@[expose] def solomonLStarOf {G : Type*} [Group G] (N : Subgroup G) : Subgroup G :=
  sSup {K | GH74.GLS.IsPCompIn 2 N K ∧ FooteLit.IsSolomonMaximal K}

@[expose] def SolomonFixedLayerStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) →
    Assembly.KProper Blueprint.Catalog G →
    ∀ (a : G) (J : Subgroup G), orderOf a = 2 → J ≤ centralizer ({a} : Set G) →
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) → GSWeakMaximalComponent J →
      IsL34Type (J ⧸ Open.fusionZStar J) → L34BaseSetting G →
      ∀ g : G, a * (g⁻¹ * a * g) = g⁻¹ * a * g * a → g⁻¹ * a * g ∈ normalizer (J : Set G) →
        (∀ j ∈ J, j⁻¹ * (g⁻¹ * a * g)⁻¹ * j * (g⁻¹ * a * g) ∈ oddIn J) →
        gsFixedLayer J (g⁻¹ * a * g) ≤
          oddIn (centralizer ({g⁻¹ * a * g} : Set G)) ⊔ conjugate J g

@[expose] def L34CenterExponentFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    ∀ z ∈ P ⊓ zStarIn J, z ^ 4 = 1

@[expose] def L34ElementaryCenterFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    (∀ z ∈ P ⊓ zStarIn J, z * z = 1) →
    ∃ E : Subgroup G, P ⊓ zStarIn J ≤ E ∧ E ≤ P ∧ IsElemTwo E ∧
      Nat.card E = 16 * Nat.card ↥(P ⊓ zStarIn J) ∧
      J ⊓ normalizer (P : Set G) ≤ normalizer (E : Set G)

@[expose] def L34TwoEightsFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    ∃ E F : Subgroup G, E ≤ P ∧ F ≤ P ∧ IsEightGroup E ∧ IsEightGroup F ∧ E ≠ F

@[expose] def L34ParabolicGenerationFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
    ∃ T₁ T₂ : Subgroup G, T₁ ≤ P ∧ T₂ ≤ P ∧ (∃ E ≤ T₁, IsEightGroup E) ∧
      (∃ E ≤ T₂, IsEightGroup E) ∧
      J ≤ oddIn J ⊔ (J ⊓ normalizer (T₁ : Set G)) ⊔ (J ⊓ normalizer (T₂ : Set G))

@[expose] def L34Lemma43EndStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsThreeConnected (S ⊓ withKernel J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        ((IsL34Type (K ⧸ Open.fusionZStar K) ∧
            J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G))) ∨
          (Nonempty (K ⧸ pPrimeCore 2 K ≃* Blueprint.NativeSporadic.He) ∧
            J ≤ K ⊔ oddIn (normalizer (W : Set G))) ∨
          (IsL34Type (K ⧸ Open.fusionZStar K) ∧ conjugate K a ≠ K ∧
            J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G)))) → False

@[expose] def L34CentralFourFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G) (x : G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J → IsL34Unitary J x →
    x ∈ normalizer (P : Set G) → ¬ IsCyclic ↥(P ⊓ zStarIn J) →
    (∃ z ∈ P ⊓ zStarIn J, z * z ≠ 1) →
    ∃ C : Subgroup G, C ≤ P ∧ IsElemTwo C ∧ Nat.card C = 16 ∧
      P ⊓ centralizer ({x} : Set G) ≤ C ∧
      (∀ y ∈ P, (∀ w ∈ P, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔ y ∈ C ⊔ (P ⊓ zStarIn J)) ∧
      normalizer (P : Set G) ≤ normalizer (C : Set G)

@[expose] def L34Lemma46WStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    L34Sec4Running J A → Monoid.exponent ↥(S ⊓ zStarIn J) = 4 → ¬ IsCyclic ↥(S ⊓ zStarIn J) →
    ∀ E : Subgroup G, E ≤ withKernel J → IsEightGroup E → wGroup E ≠ ⊥

@[expose] def L34Lemma46EndStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    ¬ IsThreeConnected (S ⊓ withKernel J) →
    Monoid.exponent ↥(S ⊓ zStarIn J) = 4 → ¬ IsCyclic ↥(S ⊓ zStarIn J) →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        ((IsL34Type (K ⧸ Open.fusionZStar K) ∧
            J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G))) ∨
          (Nonempty (K ⧸ pPrimeCore 2 K ≃* Blueprint.NativeSporadic.He) ∧
            J ≤ K ⊔ oddIn (normalizer (W : Set G))) ∨
          (IsL34Type (K ⧸ Open.fusionZStar K) ∧ conjugate K a ≠ K ∧
            J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G)))) → False

end CFSG.ComponentClassification.GrSLit
