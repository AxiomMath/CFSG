module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterSwapTMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

structure U3C1OuterSwapHigh (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T R₂ D : Subgroup G) (d : G) (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G) : Prop where
  step : U3C1OuterStepHyp G L f t T R₂ D d V 1
  level : U3C1OuterLevelData G L f t T D V U U₁ 1
  mu : ¬ U₁ ≤ centralizer (V : Set G)
  not_sylow : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U ⊔ T
  idx : ∃ b ∈ T, ∃ b' ∈ T, b ∉ szT₁ L T ⊔ zpowers t ∧ b' ∉ szT₁ L T ⊔ zpowers t ∧
    b * b'⁻¹ ∉ szT₁ L T ⊔ zpowers t
  w_mem : w ∈ T
  w_sq : w ^ 2 = 1
  w_not_mem : w ∉ szT₁ L T ⊔ zpowers t
  w_cent : ∀ r ∈ V, w * r * w⁻¹ = r
  w_not_sq : ∀ g : G, g ^ 2 ≠ w
  isPGroup : IsPGroup 2 P
  le : U ⊔ T ≤ P
  s_mem_normalizer : s ∈ normalizer ((U ⊔ T : Subgroup G) : Set G)
  s_mem : s ∈ P
  conj_t : s * t * s⁻¹ = w
  conj_w : s * w * s⁻¹ = t

theorem u3C1OuterSwapHighInput_of_false
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
      (T R₂ D : Subgroup G) (d : G) (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
      U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → False) : U3C1OuterSwapHighInput := by
  intro G _ _ L f t T R₂ D d V U U₁ hS hL hμV hnS hidx w hwT hw2 hwS hwV hsq s hsN hP hst hsw
  obtain ⟨P, hP2, hSP, hsP⟩ := hP
  exact h G L f t T R₂ D d V U U₁ w s P
    ⟨hS, hL, hμV, hnS, hidx, hwT, hw2, hwS, hwV, hsq, hP2, hSP, hsN, hsP, hst, hsw⟩

@[expose] def U3C1GmsNormInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → ∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁

@[expose] def U3C1GmsSylowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → (∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁) →
      ∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T

@[expose] def U3C1GmsFusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → (∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁) →
      (∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T) →
        ∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∈ U ⊔ T

@[expose] def U3C1GmsNotConjInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → ∀ g : G, g * t * g⁻¹ ≠ t * w

@[expose] def U3C1GmsExtremalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → (∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁) →
      (∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T) →
      (∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∈ U ⊔ T) →
      (∀ g : G, g * t * g⁻¹ ≠ t * w) →
        IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) (centralizer ({t * w} : Set G))

@[expose] def U3C1GmsClosureInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → (∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁) →
      (∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T) →
      (∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∈ U ⊔ T) →
      (∀ g : G, g * t * g⁻¹ ≠ t * w) →
      IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
        (centralizer ({t * w} : Set G)) →
        ∃ J : Subgroup G, (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ≤ J ∧
          J ≤ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) ∧
          (J = (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ∨
            J = (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓
              centralizer (((U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) :
                Subgroup G) : Set G)) ∧
          (∀ a ∈ J, ∀ b ∈ J, a * b = b * a) ∧
          ∀ a ∈ J, ∀ g ∈ centralizer ({t * w} : Set G),
            g⁻¹ * a * g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) → g⁻¹ * a * g ∈ J

@[expose] def U3C1GmsLayerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → (∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁) →
      (∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T) →
      (∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∈ U ⊔ T) →
      (∀ g : G, g * t * g⁻¹ ≠ t * w) →
      IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
        (centralizer ({t * w} : Set G)) →
      ∀ J : Subgroup G, (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ≤ J →
        J ≤ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) →
        (∀ a ∈ J, ∀ b ∈ J, a * b = b * a) →
        (∀ a ∈ J, ∀ g ∈ centralizer ({t * w} : Set G),
          g⁻¹ * a * g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) → g⁻¹ * a * g ∈ J) →
        ∃ H : Subgroup G, H ≤ centralizer ({t * w} : Set G) ∧
          H ≤ normalizer ((U₁ ⊓ centralizer ({t * w} : Set G) : Subgroup G) : Set G) ∧
          Odd (Nat.card H) ∧ D ⊓ centralizer ({t * w} : Set G) ≤ H ∧
          (∀ h₁ ∈ H, ∀ h₂ ∈ H, ∀ x ∈ U₁ ⊓ centralizer ({t * w} : Set G),
            (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹ = x) ∧
          ∀ X : Subgroup G, X ≤ U₁ ⊓ centralizer ({t * w} : Set G) →
            (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → (∀ x ∈ X, t * x * t⁻¹ ∈ X) →
              X = ⊥ ∨ X = U₁ ⊓ centralizer ({t * w} : Set G)

end CFSG.SeitzReduction.RankOne
