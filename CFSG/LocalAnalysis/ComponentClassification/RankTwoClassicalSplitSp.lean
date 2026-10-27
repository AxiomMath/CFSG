module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplit

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open

@[expose] def SymplecticSplitA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      4 ≤ D.q → ∀ (p : G) (ℓ : ℕ), 4 ≤ ℓ → D.SuzukiType p .a ℓ →
        SplitAt A (D.alpha p) D.q (fun x => D.SuzukiType x .a 2)
          fun x => D.SuzukiType x .a (ℓ - 2)

@[expose] def SymplecticTypeAPerfect : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      4 ≤ D.q → ∀ (x : G) (ℓ : ℕ), D.SuzukiType x .a ℓ →
        x ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer ({x} : Set G))

@[expose] def SymplecticPairA2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
    D.family = .symplectic → CFSG.Open.IsQuasisimple ↥A → Odd (Nat.card (center A)) →
      4 ≤ D.q → ∀ p : G, D.SuzukiType p .a 2 →
        ∃ a ∈ A, (∀ x ∈ D.alpha p, ∀ y ∈ D.alpha p, Commute x (a⁻¹ * y * a)) ∧
          (∀ x ∈ D.alpha p, ∀ y ∈ D.alpha p, x = a⁻¹ * y * a → x = 1) ∧
          ∀ x ∈ D.alpha p, x ≠ 1 → ∀ y ∈ D.alpha p, y ≠ 1 →
            D.SuzukiType (x * (a⁻¹ * y * a)) .c 2

end CFSG.ComponentClassification.RankTwoClassical
