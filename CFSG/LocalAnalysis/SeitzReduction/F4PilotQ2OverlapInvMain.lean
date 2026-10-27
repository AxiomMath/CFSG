module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapInvSwap
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapInvField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2GlobalModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.Steinberg

@[expose] def TwoOverlapInvAt (κ : Sp6Kind) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], Nat.card K = 2 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
      ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (e : L ≃* adjointGroup .F4 K) (t : G),
        F4Work L K t 1 → TwoKindAt e t X₀ κ →
          Nat.card (centralizerPerfectCore (subgroupToG e (X₀ ⊔ stdX K))) =
              twoDiagPieceOrder κ ∧
            (κ.IsGraphKind →
              coreCentCard e (X₀ ⊔ stdX K) ((Adjoint.f4Datum K).rootGroup v0120) =
                twoOverlapInvOrderL κ ∧
              coreCentCard e (X₀ ⊔ stdX K) ((Adjoint.f4Datum K).rootGroup v0110) =
                twoOverlapInvOrderS κ)

theorem twoOverlapInvKindInput_iff : TwoOverlapInvKindInput ↔ ∀ κ, TwoOverlapInvAt κ := by
  constructor
  · intro h κ K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hκ
    exact h K hK X₀ hXJ hcyc hX₀ G L e t hw κ hκ
  · intro h K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw κ hκ
    exact h κ K hK X₀ hXJ hcyc hX₀ G L e t hw hκ

theorem twoOverlapInvAt_field : TwoOverlapInvAt .field := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hκ
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact ⟨card_centralizerPerfectCore_std_field hw e hXJ hcyc hX₀ hκ,
    fun h => absurd rfl h.1⟩

theorem twoOverlapInvAt_swap : TwoOverlapInvAt .swap := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hκ
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  exact ⟨card_centralizerPerfectCore_std_swap hw e hXJ hcyc hX₀ hκ,
    fun h => absurd rfl h.2⟩

@[expose] def TwoOverlapInvGraphInput : Prop :=
  ∀ κ : Sp6Kind, κ.IsGraphKind → TwoOverlapInvAt κ

theorem twoOverlapInvKindInput_of_graphInput (h : TwoOverlapInvGraphInput) :
    TwoOverlapInvKindInput := by
  refine twoOverlapInvKindInput_iff.2 fun κ => ?_
  by_cases hg : κ.IsGraphKind
  · exact h κ hg
  · have : κ = .field ∨ κ = .swap := by
      cases κ <;> simp_all [Sp6Kind.IsGraphKind]
    rcases this with rfl | rfl
    · exact twoOverlapInvAt_field
    · exact twoOverlapInvAt_swap

theorem twoRowsCatInput_of_overlapInvGraphInput (h : TwoOverlapInvGraphInput)
    (hF : TwoFieldPairInput) (hS : TwoSwapPairInput) (hE : TwoE6PairInput)
    (hT : TwoTwistedE6PairInput) : TwoRowsCatInput :=
  twoRowsCatInput_of_overlapInvKindInput (twoOverlapInvKindInput_of_graphInput h) hF hS hE hT

end CFSG.SeitzReduction.F4Pilot
