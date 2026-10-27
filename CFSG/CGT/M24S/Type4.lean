module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.M24S

open CFSG.CGT.Timmesfeld75

@[expose] def HasType4 {G : Type} [Group G] (T : Subgroup G) : Prop :=
  ∃ x g : G, x ∈ Subgroup.normalizer (T : Set G) ∧ x ∉ T ∧ x ∈ conjSubgroup g T ∧
    Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = 4

end CFSG.CGT.M24S
