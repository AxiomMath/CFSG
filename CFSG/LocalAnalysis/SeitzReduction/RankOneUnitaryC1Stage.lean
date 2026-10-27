module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Basic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

structure U3A₁Coords {G : Type*} [Group G] {K : Type*} [Field K] (A₁ : Subgroup G) (d : G)
    (v : G → K) (μ : K) : Prop where
  mul : ∀ b ∈ A₁, ∀ b' ∈ A₁, v (b * b') = v b + v b'
  inj : ∀ b ∈ A₁, ∀ b' ∈ A₁, v b = v b' → b = b'
  surj : ∀ c : K, ∃ b ∈ A₁, v b = c
  conj_mem : ∀ b ∈ A₁, d⁻¹ * b * d ∈ A₁
  conj : ∀ b ∈ A₁, v (d⁻¹ * b * d) = μ * v b

structure U3C1Stage (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T : Subgroup G) (d : G) (V U U₁ : Subgroup G) (k : ℕ) : Prop where
  start : U3Start G L f t T
  card_sylow : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2
  T_le : T ≤ szT₁ L T ⊔ zpowers t
  one_le : 1 ≤ k
  coords : ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (v : G → K) (μ : K),
    Fintype.card K = 2 ^ f ∧ U3A₁Coords (szA₁ (szT₁ L T)) d v μ ∧
      ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w
  d_odd : Odd (orderOf d)
  d_norm : d ∈ normalizer (V : Set G) ⊓ normalizer (szT₁ L T : Set G) ⊓ centralizer ({t} : Set G)
  le_centralizer : V ≤ centralizer (szT₁ L T : Set G)
  comm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  card : Nat.card V = (2 ^ f) ^ (k + 1)
  omega : ∀ x ∈ V, x ^ 2 = 1 → x ∈ szA₁ (szT₁ L T)
  pow : ∀ x ∈ V, x ^ 2 ^ (k + 1) = 1
  le : szA₁ (szT₁ L T) ≤ V
  inv : ∀ x ∈ V, t * x * t⁻¹ = x⁻¹
  U_le : U ≤ normalizer (szR (szT₁ L T) V t : Set G)
  U_normal : normalizer (szR (szT₁ L T) V t : Set G) ≤ normalizer (U : Set G)
  isSylowOf : IsSylowOf 2 U (normalizer (szR (szT₁ L T) V t : Set G))
  card_U : Nat.card U = 2 * (2 ^ f) ^ (k + 4)
  szR_le : szR (szT₁ L T) V t ≤ U
  conj_t_not_mem : ∀ u ∈ U, u ∉ szR (szT₁ L T) V t → u * t * u⁻¹ ∉ szA L T t
  conj_szA₁ : ∀ u ∈ U, ∀ b ∈ szA₁ (szT₁ L T), u * b * u⁻¹ = b
  conj_T₁ : ∀ u ∈ U, ∀ y ∈ szT₁ L T, y⁻¹ * (u * y * u⁻¹) ∈ szA₁ (szT₁ L T)
  conj_V₁ : ∀ u ∈ U₁, ∀ r ∈ V, r⁻¹ * (u * r * u⁻¹) ∈ szA₁ (szT₁ L T)
  inf_centralizer : U ⊓ centralizer ({t} : Set G) = szT₁ L T ⊔ zpowers t
  U₁_le : U₁ ≤ U
  U₁_normal : U ≤ normalizer (U₁ : Set G)
  sup_eq : U₁ ⊔ zpowers t = U
  t_not_mem : t ∉ U₁
  inf_eq : U₁ ⊓ szR (szT₁ L T) V t = szT₁ L T ⊔ V
  d_mem_U₁ : d ∈ normalizer (U₁ : Set G)

@[expose] def U3C1OuterInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → (∃ r ∈ R₂, r ^ 2 ≠ 1) →
    ¬ T ≤ szT₁ L T ⊔ zpowers t → False

@[expose] def U3C1InnerExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → (∃ r ∈ R₂, r ^ 2 ≠ 1) →
    T ≤ szT₁ L T ⊔ zpowers t → False

theorem u3C1Exclusion_of_outer (hO : U3C1OuterInput) (hI : U3C1InnerExclusion) :
    U3C1Exclusion := by
  intro G _ _ L f t T R₂ h hS2 hR hinv hne
  by_cases hT : T ≤ szT₁ L T ⊔ zpowers t
  · exact hI G L f t T R₂ h hS2 hR hinv hne hT
  · exact hO G L f t T R₂ h hS2 hR hinv hne hT

@[expose] def U3C1RegularInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → (∃ r ∈ R₂, r ^ 2 ≠ 1) →
    T ≤ szT₁ L T ⊔ zpowers t →
    ∃ E : Subgroup G, E ≤ normalizer (szR (szT₁ L T) R₂ t : Set G) ∧
      normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (E : Set G) ∧
      szR (szT₁ L T) R₂ t ≤ E ∧ E ≤ centralizer (szA₁ (szT₁ L T) : Set G) ∧
      (∀ x ∈ E, x * t * x⁻¹ ∈ szA L T t → ∀ r ∈ R₂,
        x * (r * t) * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)) ∧
      ∀ r ∈ R₂, ∃ x ∈ E, x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)

end CFSG.SeitzReduction.RankOne
