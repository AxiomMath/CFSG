module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Statement

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ShultStronglyClosedTI

variable {X : Type} [Group X] [Finite X]

abbrev quasiHull (z : X) (V : Subgroup X) : Subgroup X :=
  Subgroup.closure (involutionPointClass z ∩ (Subgroup.normalizer (V : Set X) : Set X)) ⊔
    CFSG.Open.pCore 2 X

@[expose] def QuasiHullTwoPointOdd (Y : Subgroup X) (z : X) (V : Subgroup X) : Prop :=
  ∀ x ∈ quasiHull z V, x * x ∈ CFSG.Open.pCore 2 X → x ∉ CFSG.Open.pCore 2 X →
    ∀ ℓ ∈ quasiHull z V, ℓ ∉ Y → x ∈ Y → ℓ * x * ℓ⁻¹ ∈ Y → False

@[expose] def QuasiRankThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (u z : X),
    TheoremCBelow (Nat.card X) → CaseOneInvolutions → CoreConfig Y u z →
    ∀ (V R : Subgroup X) (z' : X), IsPGroup 2 V → CFSG.Open.pCore 2 X ≤ V →
      ¬ V ≤ CFSG.Open.pCore 2 X →
      (∀ y ∈ V, y * y ∈ CFSG.Open.pCore 2 X) → CFSG.Open.pRank 2 V = 1 →
      ¬ Subgroup.normalizer (V : Set X) ≤ Y →
      R ≤ Subgroup.normalizer (V : Set X) → R ≤ Y → IsPGroup 2 R →
      (∀ R' : Subgroup X, R' ≤ Subgroup.normalizer (V : Set X) → IsPGroup 2 R' →
        Nat.card R' ≤ Nat.card R) →
      z' ∈ R → (∀ r ∈ R, Commute r z') → z' ∈ involutionPointClass z →
      3 ≤ CFSG.Open.pRank 2 R → QuasiHullTwoPointOdd Y z V

end CFSG.ProperTwoGeneratedCore.TheoremC
