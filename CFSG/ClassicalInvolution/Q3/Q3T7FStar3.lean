module

public import CFSG.ClassicalInvolution.Uniform.UStand

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform

@[expose] def Thm7FStar3Large : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)],
    (∃ a b : genFittingFStar Y, a * b ≠ b * a) → ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) →
    CIT3Below (Nat.card Y) →
    ∀ (Ω : Set (Subgroup Y)) (K : Subgroup Y), HypOmegaModU (.sl2 3 1) Ω → K ∈ Ω →
      (∀ J ∈ Ω, ∃ g : Y, conjSub g K = J) → (⨆ J ∈ Ω, J) = ⊤ →
      (∃ K' ∈ twinSet Ω K, K' ≠ K) → IsSimpleGroup Y

end CFSG.ClassicalInvolution.Q3
