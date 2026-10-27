module

public import CFSG.GH74.Uniqueness.SU.KInputs

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.Blueprint

@[expose] def Thm231Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 → ∀ n : ℕ, (n = 9 ∨ n = 10) →
      ¬ K.IsTwoAlt ↥(centralizer ({z} : Set G)) n

end CFSG.GH74.Uniqueness.SU.SU13
