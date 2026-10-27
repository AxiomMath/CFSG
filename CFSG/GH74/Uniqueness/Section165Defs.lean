module

public import CFSG.GH74.Uniqueness.Section16Stmts

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

@[expose] def Prop165TuvStmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ (c : Conf16 Z M) (w : X), w ∈ c.D → orderOf w = 2 → w * c.u = c.u * w →
    w * c.t = c.t * w → w * c.z = c.z * w →
      IsCyclic ↥⁅zpowers c.t, c.D ⊓ cenHull Z (c.t * c.u * w)⁆

end CFSG.GH74.Uniqueness
