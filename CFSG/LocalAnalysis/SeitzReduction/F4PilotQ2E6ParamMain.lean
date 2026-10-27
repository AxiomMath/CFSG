module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ParamA
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ParamB
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RowParam

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open CFSG.LieType.Ree (ReeTag)
open CFSG.Quasithin (perfectCore perfectCore_le)

local instance f4PilotQ2E6ParamMainNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6ParamMainNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩


@[expose] def TwoE6AlignInput : Prop :=
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
        ∀ a ∈ subgroupToG e (CFSG.LieType.CurtisTits.rankOne (Adjoint.f4Datum K).rootGroup 0),
          (∀ b : e6ScLevi K {0},
            Commute a (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth zero_orth_E6) b)) ∧
          (∀ b : e6ScLevi K {2},
            Commute a (scLeviRestrict ΦA (singleton_subset_e6A5Nodes_of_orth two_orth_E6) b))

theorem twoE6ParamInput_of_alignInput (h : TwoE6AlignInput) : TwoE6ParamInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ'
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  obtain ⟨ΦA, hr, hker, hconj, hn⟩ := exists_twoGraphParamA_normalized hw e hXJ hcyc hX₀ hκ
  have hal := h G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' ΦA hr hker hconj hn
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  have hD : subgroupToG e (C3Levi K) ≤ centralizerPerfectCore (subgroupToG e X₀) := by
    rw [← perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw e hXJ hcyc hX₀']
    exact (perfectCore_le _).trans inf_le_left
  refine ⟨ΦA, twoE6ParamB e hK2, ?_⟩
  exact
    { agree := agree_twoE6ParamB e hK2 hn
      conjA := hconj
      conjB := conjB_of_range_le hw.mem_centralizer (range_twoE6ParamB_le e hK2)
      comm₀ := fun a b => (hal _ (twoE6ParamB_one_mem e hK2 a)).1 b
      comm₂ := fun a b => (hal _ (twoE6ParamB_one_mem e hK2 a)).2 b
      range_sup := sup_range_twoE6ParamB e hK2 hr hD }

theorem twoE6PairInput_of_alignInput (hA : TwoE6AlignInput) (hU : TwoE6UniqueInput) :
    TwoE6PairInput :=
  twoE6PairInput_of_paramInput (twoE6ParamInput_of_alignInput hA) hU

end CFSG.SeitzReduction.F4Pilot
