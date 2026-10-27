module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainTwLong
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2E6ChainTwMainNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def TwoTwistedE6RelayInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .unitary6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaPlus8 →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 1 F)
        (ε : h.fixedField ≃+* K)
        (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G),
        ΦX.range = centralizerPerfectCore (subgroupToG e X₀) →
        ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) →
        (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
          (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
            t * ΦX x * t⁻¹ = ΦX y) →
        IsLeviNormalizedU h ε e ΦX →
        (relayAlign K root1242 ∈ alignedSubgroup e (twLeviRestrict ΦX three_subset_X).range ∧
          relayAlign' K root1242 ∈ alignedSubgroup e (twLeviRestrict ΦX three_subset_X).range) ∧
        (relayAlign K rootE2pE3Align ∈ alignedSubgroup e (twLeviRestrict ΦX two_subset_X).range ∧
          relayAlign' K rootE2pE3Align ∈ alignedSubgroup e (twLeviRestrict ΦX two_subset_X).range)

theorem twoTwistedE6ChainInput_of_relayInput (hR : TwoTwistedE6RelayInput) :
    TwoTwistedE6ChainInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' F _ _ _ h ε ΦX hr hker hconj hn
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hXr := le_rootSL2_rootR_of_le_highestRootRankOne hXJ
  obtain ⟨⟨h3, h4⟩, ⟨h7, h8⟩⟩ :=
    hR G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' F h ε ΦX hr hker hconj hn
  exact ⟨⟨f4RootPairAlign_rootR_le_alignedTw_three h hK2 ε hXr hX₀ hr hker hn,
      f4RootPairAlign_a2_le_alignedTw_three h ε hn, h3, h4⟩,
    ⟨f4RootPairAlign_rootR_le_alignedTw_two h hK2 ε hXr hX₀ hr hker hn,
      f4RootPairAlign_e1e2_le_alignedTw_two h ε hn, h7, h8⟩⟩

end CFSG.SeitzReduction.F4Pilot
