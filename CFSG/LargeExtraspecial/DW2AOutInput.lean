module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Blueprint.Chevalley
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def IsTransClass34 {X : Type} [Group X] (D : Set X) : Prop :=
  closure D = ⊤ ∧ (∃ d₀ ∈ D, ∀ d, d ∈ D ↔ IsConj d₀ d) ∧ (∀ d ∈ D, d ≠ 1 ∧ d * d = 1) ∧
    (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4) ∧
    ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D

end CFSG.LargeExtraspecial.DW
