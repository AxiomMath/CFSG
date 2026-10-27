module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76a
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open

section Split

variable {G : Type} [Group G]

structure SplitData (A J : Subgroup G) (P₁ P₂ : G → Prop) (F : Type) [Field F]
    (ι₁ ι₂ : F → G) : Prop where
  map_add₁ : ∀ x y, ι₁ (x + y) = ι₁ x * ι₁ y
  map_add₂ : ∀ x y, ι₂ (x + y) = ι₂ x * ι₂ y
  inj₁ : ∀ x, ι₁ x = 1 → x = 0
  inj₂ : ∀ x, ι₂ x = 1 → x = 0
  mem₁ : ∀ x, ι₁ x ∈ A
  mem₂ : ∀ x, ι₂ x ∈ A
  comm : ∀ x y, Commute (ι₁ x) (ι₂ y)
  inf : ∀ x y, ι₁ x = ι₂ y → x = 0
  mem_iff : ∀ j, j ∈ J ↔ ∃ d, j = ι₁ d * ι₂ d
  prop₁ : ∀ x, x ≠ 0 → P₁ (ι₁ x)
  prop₂ : ∀ x, x ≠ 0 → P₂ (ι₂ x)
  scalar : ∀ c : F, c ≠ 0 → ∃ a ∈ A, ∀ x, a⁻¹ * ι₁ x * a = ι₁ x ∧ a⁻¹ * ι₂ x * a = ι₂ (c * x)

@[expose] def SplitAt (A J : Subgroup G) (q : ℕ) (P₁ P₂ : G → Prop) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (ι₁ ι₂ : F → G), Nat.card F = q ∧
    SplitData A J P₁ P₂ F ι₁ ι₂

end Split

@[expose] def OrthPlusSplitC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .orthPlus → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
      ∀ (p : G) (ℓ : ℕ), 4 ≤ ℓ → D.SuzukiType p .c ℓ → (Case1 D p ∨ Case4 D p) →
        SplitAt A (jGroup A p) D.q (fun x => D.SuzukiType x .a (ℓ - 2))
          fun x => D.SuzukiType x .c 2

@[expose] def OrthMinusSplitC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .orthMinus → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
      ∀ (p : G) (ℓ : ℕ), 4 ≤ ℓ → D.SuzukiType p .c ℓ → (Case1 D p ∨ Case4 D p) →
        SplitAt A (jGroup A p) D.q (fun x => D.SuzukiType x .a (ℓ - 2))
          fun x => D.SuzukiType x .c 2

@[expose] def OrthPlusSplitCTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .orthPlus → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
      ∀ p : G, D.SuzukiType p .c 2 → (Case1 D p ∨ Case4 D p) →
        SplitAt A (jGroup A p) D.q (fun x => D.SuzukiType x .a 2) fun x => D.SuzukiType x .a 2

@[expose] def OrthMinusSplitCTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .orthMinus → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) → 4 ≤ D.q →
      ∀ p : G, D.SuzukiType p .c 2 → (Case1 D p ∨ Case4 D p) →
        SplitAt A (jGroup A p) D.q (fun x => D.SuzukiType x .a 2) fun x => D.SuzukiType x .a 2

@[expose] def ClassicalSplit : Prop :=
  OrthPlusSplitC ∧ OrthMinusSplitC ∧ OrthPlusSplitCTwo ∧ OrthMinusSplitCTwo

end CFSG.ComponentClassification.RankTwoClassical
