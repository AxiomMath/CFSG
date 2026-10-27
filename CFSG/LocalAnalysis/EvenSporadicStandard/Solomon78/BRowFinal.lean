module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowW4Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowW3
public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.BabyTableIIIOf
public import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.Monster.B.CTIB.SylowCenter
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import CFSG.RankThree.PartOne.SPOR.OuterB

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.RankThree.PartOne.SPOR

theorem babyW1Commute_B : BabyW1Commute := by
  intro X hX
  obtain ⟨Y, hY2, hYr, hc⟩ := CFSG.Monster.B.CTIB.native_B_involution_commutes_rank_1860 X hX
  have hconj : IsConj Y (babyRep 1) := isConj_rep_one_of_rank hY2 hYr
  exact ⟨Y, BabyInv.of_isConj babyInv_zero_babyRep_one hconj.symm, hc.eq.symm⟩

theorem babySylowCenter_B : BabySylowCenter := by
  have := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨-, hT, -⟩ := CFSG.Monster.B.CTIB.native_B_sylow_two_center
  obtain T : Sylow 2 B := default
  obtain ⟨-, Z, hZ2, hZr, hZc⟩ := hT T
  have hZmem : Z ∈ (center (T : Subgroup B)).map (T : Subgroup _).subtype := by
    rw [hZc]
    exact mem_zpowers Z
  refine ⟨T, Z, babyInv_one_of_rank_2048 hZ2 hZr, fun p hp => ?_, fun z hz hzc => ?_⟩
  · obtain ⟨z', hz', hz'Z⟩ := hZmem
    have := mem_center_iff.1 hz' ⟨p, hp⟩
    have h := congrArg Subtype.val this
    rw [← hz'Z]
    exact h
  · have hz' : z ∈ (center (T : Subgroup B)).map (T : Subgroup _).subtype :=
      ⟨⟨z, hz⟩, mem_center_iff.2 fun g => Subtype.ext (hzc g g.2), rfl⟩
    rw [hZc] at hz'
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz'
    rcases zpow_eq_one_or_self_of_orderOf_eq_two hZ2 k with h1 | h1
    · exact Or.inl (hk.symm.trans h1)
    · exact Or.inr (hk.symm.trans h1)

theorem babyCenterW4_B : BabyCenterW4 := by
  have := CFSG.Monster.B.Pinned.finite_B
  exact fun a ha => centerInvAt_babyInv_three babyTableIII babyTableIV babyW1Commute_B
    babyF4Subgroup_B ha

theorem babyCenterW3_B : BabyCenterW3 := by
  intro a ha
  have h3 : BabyInv 2 (babyRep 3) :=
    ⟨orderOf_babyRep (by norm_num), natCard_centralizer_rep_three⟩
  refine CenterInvAt.of_isConj (babyTableIII.2 2 a (babyRep 3) ha h3) ?_
  have h := @CenterInvAt.of_mulEquiv CFSG.Monster.B.Sbp CFSG.Blueprint.NativeSporadic.B _
    Units.instGroup CFSG.Monster.B.CTIB.iotaEquiv.symm _ centerInvAt_qS_seven
  rw [← CFSG.Monster.B.CTIB.rs3_eq] at h
  exact h

theorem b_data_of_simple {Y : Type} [Group Y] (e : Y ≃* Carrier .B) :
    AllInner Y ∧ CenterInvolutions Y ∧ InvolutionsCommute Y := by
  have := CFSG.Monster.B.Pinned.finite_B
  have hT3 := babyTableIII
  refine ⟨AllInner.of_mulEquiv e.symm allInner_B, ?_, ?_⟩
  · exact CenterInvolutions.of_mulEquiv (e := e.symm)
      (centerInvolutions_baby hT3 babyTableIV babySylowCenter_B babyCenterW3_B babyCenterW4_B)
  · exact InvolutionsCommute.of_mulEquiv e.symm
      (involutionsCommute_baby hT3 babyW1Commute_B babySylowCenter_B babyW3W4Commute_B)

end CFSG.EvenSporadicStandard.Solomon78
