module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3TMFSBasic
public import CFSG.ClassicalInvolution.Uniform.UStand
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3T.MFS

section Targets

@[expose] def FrameExitSp62 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (T : Subgroup Y), T.Normal →
    Subgroup.centralizer (T : Set Y) = ⊥ → Models.LieModel ↥T .PSp 3 2 1 → T = ⊤

@[expose] def FStarTwinMemberFreeLarge : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)],
    (∃ a b : genFittingFStar Y, a * b ≠ b * a) → CIT3Below (Nat.card Y) →
    ∀ (Ω : Set (Subgroup Y)) (K : Subgroup Y), HypOmegaModU (.sl2 3 1) Ω → K ∈ Ω →
      (∀ J ∈ Ω, ∃ g : Y, conjSub g K = J) → (⨆ J ∈ Ω, J) = ⊤ →
      (∃ K' ∈ twinSet Ω K, K' ≠ K) → genFittingFStar Y ⊔ K = ⊤ →
      (∀ (z' : genFittingFStar Y) (L' : Subgroup (genFittingFStar Y)),
        ¬ IsClassicalMember3 L' z') →
      memberIndex K (genFittingFStar Y) = 3 →
      ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) → False

@[expose] def FrameExitD42 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)],
    (∃ a b : genFittingFStar Y, a * b ≠ b * a) → CIT3Below (Nat.card Y) →
    ∀ (Ω : Set (Subgroup Y)) (K : Subgroup Y), HypOmegaModU (.sl2 3 1) Ω → K ∈ Ω →
      (∀ J ∈ Ω, ∃ g : Y, conjSub g K = J) → (⨆ J ∈ Ω, J) = ⊤ →
      (∃ K' ∈ twinSet Ω K, K' ≠ K) → genFittingFStar Y ⊔ K = ⊤ →
      (∀ (z' : genFittingFStar Y) (L' : Subgroup (genFittingFStar Y)),
        ¬ IsClassicalMember3 L' z') →
      memberIndex K (genFittingFStar Y) = 3 →
      Models.LieModel ↥(genFittingFStar Y) .POmegaPlus 4 2 1 → False

end Targets

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
