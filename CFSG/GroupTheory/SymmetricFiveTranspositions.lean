module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.GroupTheory

open Equiv

@[expose] def transpositions : Set (Equiv.Perm (Fin 5)) := {τ | τ.IsSwap}

private instance instDecidablePredIsSwap :
    DecidablePred (fun σ : Equiv.Perm (Fin 5) => σ.IsSwap) :=
  fun σ =>
    decidable_of_iff (∃ x y : Fin 5, x ≠ y ∧ σ = Equiv.swap x y) Iff.rfl

theorem card_transpositions : Nat.card {τ : Equiv.Perm (Fin 5) // τ.IsSwap} = 10 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private instance instDecidableRelCommutePermFin5 :
    DecidableRel (fun σ τ : Equiv.Perm (Fin 5) => Commute σ τ) :=
  fun σ τ => decidable_of_iff (σ * τ = τ * σ) Iff.rfl

private theorem fintype_card_commuting_transpositions :
    ∀ τ : Equiv.Perm (Fin 5), τ.IsSwap →
      Fintype.card {σ : Equiv.Perm (Fin 5) // σ.IsSwap ∧ σ ≠ τ ∧ Commute σ τ} = 3 := by
  decide +kernel

theorem card_transpositions_commuting (τ : Equiv.Perm (Fin 5)) (hτ : τ.IsSwap) :
    Nat.card {σ : Equiv.Perm (Fin 5) // σ.IsSwap ∧ σ ≠ τ ∧ Commute σ τ} = 3 := by
  rw [Nat.card_eq_fintype_card]
  exact fintype_card_commuting_transpositions τ hτ

theorem reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hsymm : ∀ a b, r a b → r b a) {a b : α} (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih

def nc (σ τ : Equiv.Perm (Fin 5)) : Prop :=
  σ.IsSwap ∧ τ.IsSwap ∧ σ ≠ τ ∧ ¬ Commute σ τ

private instance instDecidableRelNc :
    DecidableRel (nc : Equiv.Perm (Fin 5) → Equiv.Perm (Fin 5) → Prop) :=
  fun σ τ =>
    decidable_of_iff (σ.IsSwap ∧ τ.IsSwap ∧ σ ≠ τ ∧ σ * τ ≠ τ * σ) Iff.rfl

end CFSG.GroupTheory
