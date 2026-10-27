module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEndInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

@[expose] def HeldOuterSolvableFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) →
    Group.IsSolvable (OuterAutomorphisms.Outer ↥L)

@[expose] def HeldInvolAutFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) →
    ∀ n ∈ normalizer (L : Set X), n * n ∈ centralizer (L : Set X) →
      n ∉ centralizer (L : Set X) →
      (∃ y ∈ L, orderOf y = 2 ∧ y⁻¹ * n ∈ centralizer (L : Set X)) ∨
      ((∀ y ∈ L, y⁻¹ * n ∉ centralizer (L : Set X)) ∧
        (∃ w : X, HeldTwoA L w ∧ n * w = w * n) ∧
        (∀ S : Subgroup X, S ≤ L → S ≤ centralizer ({n} : Set X) → Nat.card S ≤ 15120) ∧
        ∃ Q : Subgroup X, Q ≤ L ∧ Q ≤ centralizer ({n} : Set X) ∧ ⁅Q, Q⁆ = Q ∧
          Nat.card Q = 7560 ∧ Nat.card (center ↥Q) = 3 ∧ IsSimpleGroup (↥Q ⧸ center ↥Q) ∧
          ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ * q₁ = 1 ∧ q₂ * q₂ = 1 ∧ q₁ ≠ 1 ∧ q₂ ≠ 1 ∧ q₁ ≠ q₂ ∧
            q₁ * q₂ = q₂ * q₁)

@[expose] def HeldTwoAKFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) → ∀ u : X, HeldTwoA L u →
      Nat.card (center ↥(gsFixedLayer L u)) = 4 ∧
      (∀ S : Subgroup X, S ≤ L ⊓ centralizer ({u} : Set X) → ⁅S, S⁆ = S →
        S ≤ gsFixedLayer L u) ∧
      ∀ y ∈ L, (∀ k ∈ gsFixedLayer L u, y * k = k * y) →
        y = 1 ∨ (HeldTwoA L y ∧ y ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype)

@[expose] def HeldTwoBFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) →
    ∀ v ∈ L, orderOf v = 2 → gsFixedLayer L v = ⊥ →
      Nat.card ↥(L ⊓ centralizer ({v} : Set X)) = 21504 ∧
      ∀ N : Subgroup X, N ≤ L ⊓ centralizer ({v} : Set X) →
        (N.subgroupOf (L ⊓ centralizer ({v} : Set X))).Normal →
        N ≠ L ⊓ centralizer ({v} : Set X) → IsPGroup 2 N

@[expose] def HeldSylowFourFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X),
    Nonempty (L ≃* Blueprint.NativeSporadic.He) →
    ∀ T : Subgroup X, T ≤ L → Nat.card T = 1024 →
      ∀ N : Subgroup X, N ≤ T → (N.subgroupOf T).Normal → 4 ≤ Nat.card N →
        ∃ y₁ ∈ N, ∃ y₂ ∈ N, y₁ * y₁ = 1 ∧ y₂ * y₂ = 1 ∧ y₁ ≠ 1 ∧ y₂ ≠ 1 ∧ y₁ ≠ y₂ ∧
          y₁ * y₂ = y₂ * y₁

end CFSG.ComponentClassification.GrSLit
