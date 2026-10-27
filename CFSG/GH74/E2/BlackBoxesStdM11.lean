module

public import CFSG.GH74.E2.Shapes

public section

namespace CFSG.GH74.E2

open Subgroup

@[expose] def AschbacherStandardM11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → KGH G →
    ∀ K : Subgroup G, CFSG.IsStandardSubgroup K → ShapeM11 ↥K →
      (∃ u v : G, orderOf u = 2 ∧ orderOf v = 2 ∧ u ≠ v ∧ u * v = v * u ∧
        u ∈ centralizer (K : Set G) ∧ v ∈ centralizer (K : Set G)) → False

end CFSG.GH74.E2
