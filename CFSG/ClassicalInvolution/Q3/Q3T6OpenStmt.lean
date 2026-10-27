module

public import CFSG.ClassicalInvolution.Q3.Q3CLApi

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

@[expose] def MuS3OfShape3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Q3CL.PartIHypG Ω →
    ∀ W ∈ WSet Ω, Disconnected.DEdgeless Ω → (∃ K ∈ Ω, (omegaStarNbr Ω K).Nonempty) →
      MuIsoS3 Ω W

@[expose] def MuZ2OfShape3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Q3CL.PartIHypG Ω →
    ∀ W ∈ WSet Ω, Ω.Nonempty → (∀ K ∈ Ω, omegaStarNbr Ω K = ∅) → MuIsoZ2 Ω W

end CFSG.ClassicalInvolution.Q3.Q3T6
