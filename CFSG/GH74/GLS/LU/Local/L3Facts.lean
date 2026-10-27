module

public import CFSG.GH74.GLS.IVK.Statements.Sec4

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def L3InvTorus : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (δ : ℤ) (q : ℕ), (δ = 1 ∨ δ = -1) → Odd q → 5 ≤ q →
    IsLnEps 3 J δ q → ∀ a b : J, orderOf a = 2 → orderOf b = 2 → a ≠ b → a * b = b * a →
      (Nat.card ↥(centralizer ({b} : Set J) ⊓ Ez a) : ℤ) = (q : ℤ) - δ

@[expose] def L3Cover : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (δ : ℤ) (p n : ℕ), p.Prime → p ≠ 2 → (δ = 1 ∨ δ = -1) →
    5 ≤ p ^ n → IsLnEps 3 J δ (p ^ n) →
    ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E → ∀ π : E →* J, Function.Surjective π →
      π.ker ≤ Subgroup.center E →
      (δ = 1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ n ∧
        ∃ α : SL(3, F) →* E, Function.Surjective α) ∧
      (δ = -1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (p ^ n) ^ 2 ∧
        ∃ α : ↥(StatedSU 3 (p ^ n) F) →* E, Function.Surjective α)

end CFSG.GH74.GLS.LU.Local
