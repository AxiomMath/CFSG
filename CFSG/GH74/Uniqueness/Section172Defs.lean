module

public import CFSG.GH74.Uniqueness.Section16Stmts

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

section Stmts

variable (Z : Set X) (M : Subgroup X)

@[expose] def Lemma172aBStmt : Prop :=
  ∀ (c : Conf16 Z M) (n i e : ℕ), BenderSub Z M (cenHull Z c.u) n i e →
    ((c.D ⊓ cenHull Z c.u) ⊓ centralizer ({c.t} : Set X)).relIndex (c.D ⊓ cenHull Z c.u) =
      2 ^ n - 1

@[expose] def Lemma172PStmt : Prop :=
  ∀ (c : Conf16 Z M) (n i e : ℕ), BenderSub Z M (cenHull Z c.u) n i e →
    Nat.card ↥c.P = (2 ^ n) ^ i

@[expose] def Lemma172gStmt : Prop :=
  ∀ (c : Conf16 Z M) (n i e : ℕ), BenderSub Z M (cenHull Z c.u) n i e →
    (c.D ⊓ centralizer ({c.t, c.u} : Set X)).relIndex
        (c.D ⊓ centralizer ({c.t * c.u} : Set X)) =
      ((c.D ⊓ cenHull Z (c.t * c.u)) ⊓ centralizer ({c.t} : Set X)).relIndex
        (c.D ⊓ cenHull Z (c.t * c.u))

end Stmts

end CFSG.GH74.Uniqueness
