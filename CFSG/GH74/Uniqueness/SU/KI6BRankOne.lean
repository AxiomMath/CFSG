module

public import CFSG.GH74.Uniqueness.SU.KI6BFacts
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace RankOneAux

theorem oddCore_eq_bot {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {z : K}
    (hz : orderOf z = 2) (hc : IsPGroup 2 ↥(center K)) : CFSG.oddCore K = ⊥ := by
  have hle : CFSG.oddCore K ≤ center K := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hK
        (inferInstance : (CFSG.oddCore K).Normal) with h | h
    · exact absurd (h ▸ mem_top z) (CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hz)
    · exact h
  refine eq_bot_iff.2 fun x hx => ?_
  rw [mem_bot]
  obtain ⟨k, hk⟩ := hc ⟨x, hle hx⟩
  have hxk : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, OneMemClass.coe_one] at this
  have hodd : Odd (orderOf x) :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.odd_card_oddCore.of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hx)
  exact RankOneCover.eq_one_of_odd_orderOf_of_pow hodd hxk

theorem exists_data {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hrank : CFSG.pRank 2 K ≤ 1) (hc : IsPGroup 2 ↥(center K)) :
    ∃ z : K, orderOf z = 2 ∧ (∀ y : K, orderOf y = 2 → y = z) ∧ center K = zpowers z ∧
      ∃ (S : Sylow 2 K) (r : ℕ), 3 ≤ r ∧ Nonempty (S ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨-, ⟨z, hz, hzuniq⟩, hcentral, hsyl⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.quasisimple_rank_one_unique_central_involution hK hrank
  have huniq : ∀ y : K, orderOf y = 2 → y = z := fun y hy => hzuniq y hy
  have hZ : center K = zpowers z :=
    RankOneCover.center_eq_zpowers (oddCore_eq_bot hK hz hc) (hcentral z hz) huniq hsyl
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨r, hr, he⟩ := hsyl S₀
  exact ⟨z, hz, huniq, hZ, S₀, r, hr, he⟩

end RankOneAux

theorem rankOne_facts : RankOneFacts := by
  intro K _ _ hK hrank hcenter
  obtain ⟨z, hz, huniq, hZ, S₀, r, hr, ⟨e₀⟩⟩ := RankOneAux.exists_data hK hrank hcenter
  refine ⟨z, hz, huniq, hZ, ?_, hK.2.1, ?_⟩
  · have : NeZero (2 ^ (r - 2)) := ⟨(Nat.two_pow_pos _).ne'⟩
    refine ⟨(e₀.symm (QuaternionGroup.xa 0)).1, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_xa 0
  · intro P
    obtain ⟨eD⟩ := RankOneCover.image_sylow_dihedral hz hZ S₀ hr e₀
    exact ⟨r - 2, by omega, ⟨(Sylow.equiv P (S₀.mapSurjective
      (QuotientGroup.mk'_surjective (center K)))).trans eD⟩⟩

theorem rankOne_sl25 : RankOneSL25 := by
  intro K _ _ hK hrank hcenter hA5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨z, hz, huniq, hZ, S₀, r, hr, ⟨e₀⟩⟩ := RankOneAux.exists_data hK hrank hcenter
  obtain ⟨e⟩ := hA5
  obtain ⟨e5⟩ := CFSG.SectionRank.Ccomm.projective_five_alternating
  have hk : ringChar (ZMod 5) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    norm_num
  obtain ⟨F, -, -⟩ := RankOneCover.central_double_cover hz (hZ ▸ mem_zpowers z) hZ S₀ hr e₀
    (ZMod 5) hk
    (e.trans (e5.symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        2 (ZMod 5))))
  unfold IsSL25
  exact ⟨ZMod 5, inferInstance, inferInstance, by rw [Nat.card_zmod],
    ⟨F.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (ZMod 5))⟩⟩

end CFSG.GH74.Uniqueness.SU.K.R6
