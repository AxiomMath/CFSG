module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainLong
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6AlignGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2E6ChainMainNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6ChainMainNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

theorem le_rootSL2_rootR_of_le_highestRootRankOne {K : Type} [Field K] [CharP K 2]
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) :
    X₀ ≤ rootSL2 K rootR := by
  rw [rootSL2_rootR, ← highestRootRankOne_eq_rootSL2R]
  exact hXJ

@[expose] def TwoE6RelayInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .linear6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaMinus8 →
      ∀ ΦA : e6ScLevi K e6A5Nodes →* G,
        ΦA.range = centralizerPerfectCore (subgroupToG e X₀) →
        ΦA.ker ≤ center (e6ScLevi K e6A5Nodes) →
        (∀ x y : e6ScLevi K e6A5Nodes,
          (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y) →
        IsLeviNormalizedA e ΦA →
        (relayAlign K root1242 ∈ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range ∧
          relayAlign' K root1242 ∈ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6)).range) ∧
        (relayAlign K rootE2pE3Align ∈ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range ∧
          relayAlign' K rootE2pE3Align ∈ alignedSubgroup e
            (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6)).range)

theorem twoE6ChainInput_of_relayInput (h : TwoE6RelayInput) : TwoE6ChainInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' ΦA hr hker hconj hn
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hXr := le_rootSL2_rootR_of_le_highestRootRankOne hXJ
  obtain ⟨⟨h3, h4⟩, ⟨h7, h8⟩⟩ := h G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' ΦA hr hker hconj hn
  exact ⟨⟨f4RootPairAlign_rootR_le_aligned_zero hK2 hXr hX₀ hr hker hn,
      f4RootPairAlign_a2_le_aligned_zero hn, h3, h4⟩,
    ⟨f4RootPairAlign_rootR_le_aligned_two hK2 hXr hX₀ hr hker hn,
      f4RootPairAlign_e1e2_le_aligned_two hn, h7, h8⟩⟩

theorem twoE6PairInput_of_relayInput (h : TwoE6RelayInput) (hU : TwoE6UniqueInput) :
    TwoE6PairInput :=
  twoE6PairInput_of_chainInput' (twoE6ChainInput_of_relayInput h) hU

end CFSG.SeitzReduction.F4Pilot
