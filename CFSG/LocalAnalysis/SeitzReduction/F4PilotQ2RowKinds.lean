module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie

@[expose] def TwoKindAt {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    (e : L ≃* adjointGroup .F4 K) (t : G) (X₀ : Subgroup (adjointGroup .F4 K)) (κ : Sp6Kind) :
    Prop :=
  ∃ htX : t ∈ centralizer (subgroupToG e X₀ : Set G),
    NeighbourOvergroupKind
      (QuotientGroup.mk' (oddCore (centralizer (subgroupToG e X₀ : Set G))) ⟨t, htX⟩)
      (((subgroupToG e (C3Levi K)).subgroupOf (centralizer (subgroupToG e X₀ : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (subgroupToG e X₀ : Set G))))) 1 κ

end CFSG.SeitzReduction.F4Pilot
