module

public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

@[expose] def CentralizersInSubgroup (Ω : Set (Subgroup G)) (K W H : Subgroup G) : Prop :=
  ∀ J ∈ KPerp Ω K, ∀ a ∈ K ⊔ J, a ∈ W → a ≠ 1 → a * a = 1 →
    Subgroup.centralizer ({a} : Set G) ≤ H

end CFSG.ClassicalInvolution.Asc77
