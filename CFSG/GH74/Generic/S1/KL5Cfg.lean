module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic

public section

open Subgroup CFSG CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.Generic.S1

@[expose] def KL5Cfg {S : Type} [Group S] (A B : Subgroup S) (p f : ℕ) : Prop :=
  (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ CFSG.IsQuasisimple ↥A ∧ CFSG.IsQuasisimple ↥B ∧ p.Prime ∧
    p ≠ 2 ∧ 5 ≤ p ^ f ∧
    (StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSL 3 p f ∨
      StatedClassicalModel (↥A ⧸ Subgroup.center ↥A) .PSU 3 p f) ∧
    StatedClassicalModel (↥B ⧸ Subgroup.center ↥B) .PSL 2 p f

end CFSG.GH74.Generic.S1
