module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.CGT.PushingUpLit.SolKAb

abbrev sylowImg {G : Type} [Group G] {K : Subgroup G} (R : Sylow 2 K) : Subgroup G :=
  (R : Subgroup K).map K.subtype

@[expose] def IsCommSubgroup {G : Type} [Group G] (A : Subgroup G) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a * b = b * a

theorem isPGroup_sylowImg {G : Type} [Group G] {K : Subgroup G} (R : Sylow 2 K) :
    IsPGroup 2 (sylowImg R) :=
  R.isPGroup'.map K.subtype

end CFSG.CGT.PushingUpLit.SolKAb
