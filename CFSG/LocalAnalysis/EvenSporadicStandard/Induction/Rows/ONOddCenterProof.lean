module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOInputs
public import CFSG.Sporadic.Recognition.ONMultiplierCert

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

theorem isPGroup_two_center_of_oddCore_eq_bot {Q : Type} [Group Q] [Finite Q]
    (h : CFSG.oddCore Q = ⊥) : IsPGroup 2 (center Q) := by
  intro g
  have hg : orderOf (g : Q) ≠ 0 := orderOf_ne_zero_iff.2 (isOfFinOrder_of_finite _)
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hg
  refine ⟨k, ?_⟩
  set y : Q := (g : Q) ^ 2 ^ k with hy
  have hyc : y ∈ center Q := pow_mem g.2 _
  have hord : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (by positivity) ⟨m, hkm⟩, hkm, Nat.mul_div_cancel_left _
      (by positivity)]
  have hnorm : (zpowers y).Normal := ⟨fun n hn x => by
    have hnc : n ∈ center Q := Subgroup.zpowers_le.2 hyc hn
    rw [mem_center_iff.1 hnc x, mul_inv_cancel_right]
    exact hn⟩
  have hodd : Odd (Nat.card (zpowers y)) := by
    rw [Nat.card_zpowers, hord]
    exact hm
  have hle := le_oddCore_of_normal_odd hnorm hodd
  rw [h, le_bot_iff, zpowers_eq_bot] at hle
  have : orderOf y = 1 := by rw [hle, orderOf_one]
  have hm1 : m = 1 := hord ▸ this
  have : (g : Q) ^ 2 ^ k = 1 := by
    rw [← hy, ← orderOf_eq_one_iff, hord, hm1]
  exact Subtype.ext this


theorem onOddCenter_of_certificate : ONOddCenter := by
  intro X _ _ hq hX
  have hperf : Group.IsPerfect X := hq.1
  have hker : (QuotientGroup.mk' (CFSG.oddCore X)).ker ≤ center X := by
    rw [QuotientGroup.ker_mk']
    exact oddCore_le_center hq
  have hQperf : Group.IsPerfect (X ⧸ CFSG.oddCore X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.oddCore X))
      (QuotientGroup.mk'_surjective _)
  have hO : CFSG.oddCore (X ⧸ CFSG.oddCore X) = ⊥ := oddCore_quotient_eq_bot
  have hZ2 : IsPGroup 2 (center (X ⧸ CFSG.oddCore X)) :=
    isPGroup_two_center_of_oddCore_eq_bot hO
  obtain ⟨e₁⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore X))
    (QuotientGroup.mk'_surjective _) hker
  obtain ⟨e₂⟩ := hX
  have hbot := CFSG.Sporadic.Recognition.ONMultiplier.center_eq_bot_of_certificate hQperf hZ2
    (e₁.symm.trans e₂)
  have h := card_center_eq_of_cover (QuotientGroup.mk' (CFSG.oddCore X))
    (QuotientGroup.mk'_surjective _) hker
  rw [QuotientGroup.ker_mk', hbot, Subgroup.card_bot, mul_one] at h
  rw [h]
  exact odd_card_oddCore' X

end CFSG.EvenSporadicStandard.Induction
