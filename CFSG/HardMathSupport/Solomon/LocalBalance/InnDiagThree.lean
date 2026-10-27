module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open

@[expose] def IsConjByGL {K : Type} [Field K] (H : Subgroup (GL (Fin 3) K))
    (φ : MulAut (StatedProj H)) : Prop :=
  ∃ g : GL (Fin 3) K, g ∈ Subgroup.normalizer (H : Set (GL (Fin 3) K)) ∧
    ∀ A A' : ↥H, (A' : GL (Fin 3) K) = g * (A : GL (Fin 3) K) * g⁻¹ →
      φ (QuotientGroup.mk A) = QuotientGroup.mk A'

@[expose] def IsInnDiagPSL3 {Y : Type*} [Group Y] (α : MulAut Y) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K)
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL 3 K))
    (φ : MulAut (StatedProj (StatedSL 3 K))), IsConjByGL (StatedSL 3 K) φ ∧
      ∀ y : Y, θ (QuotientGroup.mk (α y)) = φ (θ (QuotientGroup.mk y))

@[expose] def IsInnDiagPSU3 {Y : Type*} [Group Y] (α : MulAut Y) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ)
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU 3 q K))
    (φ : MulAut (StatedProj (StatedSU 3 q K))), Nat.card K = q ^ 2 ∧
      IsConjByGL (StatedSU 3 q K) φ ∧
      ∀ y : Y, θ (QuotientGroup.mk (α y)) = φ (θ (QuotientGroup.mk y))

@[expose] def IsInnDiagThree {Y : Type*} [Group Y] (α : MulAut Y) : Prop :=
  IsInnDiagPSL3 α ∨ IsInnDiagPSU3 α

@[expose] def IsThreeType (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU 3 q K)))

end CFSG.HardMathSupport.Solomon.LocalBalance
