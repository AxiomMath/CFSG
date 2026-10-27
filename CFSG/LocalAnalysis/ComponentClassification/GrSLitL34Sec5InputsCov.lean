module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34SylowCentralizerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G) (g : G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K → g ∈ normalizer (K : Set G) →
    (∀ p ∈ P, g * p = p * g) →
    ∃ k ∈ P, k⁻¹ * g ∈ coreActionKernel K ∧ ∀ p ∈ P, k⁻¹ * p⁻¹ * k * p ∈ zStarIn K

@[expose] def L34CenterRankFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
    Nat.card ↥(omegaOne (P ⊓ zStarIn K)) ≤ 4

@[expose] def L34CenterNoncyclicFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K → ¬ IsCyclic ↥(P ⊓ zStarIn K) →
    (∃ z ∈ P ⊓ zStarIn K, z * z ≠ 1) →
    P ⊓ centralizer (P : Set G) = P ⊓ zStarIn K

@[expose] def L34ElementaryCenterSylowFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
    (∀ z ∈ P ⊓ zStarIn K, z * z = 1) →
    IsElemTwo (P ⊓ centralizer (P : Set G)) ∧
      Nat.card ↥(P ⊓ centralizer (P : Set G)) = 4 * Nat.card ↥(P ⊓ zStarIn K) ∧
      P ⊓ centralizer (P : Set G) ≤ ⁅P, P⁆

@[expose] def L34UnitaryAutFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K R : Subgroup G) (x : G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsL34Unitary K x → IsPGroup 2 R →
    R ≤ normalizer (K : Set G) ⊓ centralizer ({x} : Set G) →
    Nat.card R ≤ 32 * Nat.card ↥(R ⊓ coreActionKernel K) ∧
    (∀ E : Subgroup G, E ≤ R → IsElemTwo E →
      Nat.card E ≤ 8 * Nat.card ↥(E ⊓ coreActionKernel K)) ∧
    ∀ y ∈ R, y * y ∉ coreActionKernel K → ∀ a ∈ R, ∀ b ∈ R, a * y = y * a → b * y = y * b →
      a⁻¹ * b⁻¹ * a * b ∈ coreActionKernel K

@[expose] def L2UnbalancingAutFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J R : Subgroup G), GSUnbalancingTriple a x J →
    (IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J)) → IsPGroup 2 R →
    (R ≤ normalizer (J : Set G) ⊓ centralizer ({x} : Set G) →
      (∀ y ∈ R, y * y ∈ coreActionKernel J) ∧
        Nat.card R ≤ 4 * Nat.card ↥(R ⊓ coreActionKernel J)) ∧
    (R ≤ J ⊓ centralizer ({x} : Set G) → Nat.card R ≤ 2)

@[expose] def L34UnitaryCenterFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G) (x : G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsL34Unitary K x → IsSylowTwoIn P K →
    x ∈ normalizer (P : Set G) → (∀ z ∈ P ⊓ zStarIn K, z * z = 1) →
    Nat.card ↥(P ⊓ centralizer (P : Set G) ⊓ centralizer ({x} : Set G)) =
      2 * Nat.card ↥(P ⊓ zStarIn K) ∧
    (P ⊓ zStarIn K = ⊥ → ∀ w ∈ P ⊓ centralizer (P : Set G) ⊓ centralizer ({x} : Set G),
      ∃ v ∈ P ⊓ centralizer (P : Set G), v⁻¹ * x⁻¹ * v * x = w)

@[expose] def L34AutSylowCenterFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K S : Subgroup G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn S (normalizer (K : Set G)) →
    (∀ z ∈ S ⊓ zStarIn K, z * z = 1) →
    (∀ y ∈ S, ∀ S₁ : Subgroup G, S₁ ≤ S → Nat.card S ≤ 2 * Nat.card S₁ →
      (∀ s ∈ S₁, s⁻¹ * y⁻¹ * s * y ∈ coreActionKernel K) →
      y ∈ (S ⊓ K ⊓ centralizer ((S ⊓ K : Subgroup G) : Set G)) ⊔ (S ⊓ coreActionKernel K)) ∧
    ∀ E : Subgroup G, S ⊓ coreActionKernel K ≤ E → E ≤ S → S ≤ normalizer (E : Set G) →
      (∀ e ∈ E, ∀ f ∈ E, e⁻¹ * f⁻¹ * e * f ∈ coreActionKernel K ∧ e * e ∈ coreActionKernel K) →
      8 * Nat.card ↥(S ⊓ coreActionKernel K) ≤ Nat.card E →
      S ⊓ K ⊓ centralizer ((S ⊓ K : Subgroup G) : Set G) ≤ E

@[expose] def L34MaxElementaryThreeFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P A : Subgroup G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
    (∀ z ∈ P ⊓ zStarIn K, z * z = 1) → A ≤ P → IsElemTwo A →
    Nat.card A = 16 * Nat.card ↥(P ⊓ zStarIn K) →
    ∃ f ∈ K, Odd (orderOf f) ∧ f ∈ normalizer (A : Set G) ∧
      A ⊓ centralizer ({f} : Set G) = P ⊓ zStarIn K ∧
      ∃ A₀ : Subgroup G, A₀ ≤ A ∧ Nat.card A₀ = 16 ∧ A₀ ⊓ zStarIn K = ⊥ ∧
        f ∈ normalizer (A₀ : Set G) ∧ A₀ ⊓ centralizer ({f} : Set G) = ⊥

end CFSG.ComponentClassification.GrSLit
