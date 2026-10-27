module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BRowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CentralLift
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoMultiplierRow
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std

section Rank

theorem e6CoverRank_proved : E6CoverRank := by
  intro X _ _ hq hlm
  obtain ⟨e⟩ := (CFSG.EvenSmallLie.TwoE6.lieModel_twistedE6_two_iff _).1 hlm
  have hZ12 : Nat.card (center X) ∣ 12 := by
    have h1 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
    rwa [CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover.card_hopfMultiplier] at h1
  have hr : ∀ A : Subgroup X, A ≤ (QuotientGroup.mk' (center X)).ker →
      (∀ a ∈ A, a * a = 1) → Nat.card A ≤ 2 ^ 2 := by
    intro A hA hsq
    rw [QuotientGroup.ker_mk'] at hA
    exact card_le_two_pow_of_dvd hsq ((Subgroup.card_dvd_of_le hA).trans hZ12) (by norm_num)
  have hle : radicalZ ≤ stdGroup := fun g hg => (radicalQ_le_groupJ (radicalZ_le_radicalQ hg)).1
  let Zs : Subgroup ↥stdGroup := radicalZ.subgroupOf stdGroup
  let V : Subgroup (X ⧸ center X) := Zs.map e.symm.toMonoidHom
  have hVcard : Nat.card V = 2 ^ 7 := by
    rw [Nat.card_congr (Zs.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact card_radicalZ
  have hVE : IsElementaryAbelian 2 V := by
    refine isElementaryAbelian_of_sq_eq_one V ?_ ?_
    · rintro _ ⟨z₁, hz₁, rfl⟩ _ ⟨z₂, hz₂, rfl⟩
      have := mul_comm_of_mem_radicalZ hz₁ hz₂
      show e.symm z₁ * e.symm z₂ = e.symm z₂ * e.symm z₁
      rw [← map_mul, ← map_mul]
      exact congrArg e.symm (Subtype.ext this)
    · rintro _ ⟨z, hz, rfl⟩
      have := mul_self_of_mem_radicalZ hz
      show e.symm z * e.symm z = 1
      rw [← map_mul]
      have h1 : z * z = 1 := Subtype.ext this
      rw [h1, map_one]
  obtain ⟨A, hA, k, hk3, hAk⟩ := exists_elementaryAbelian_of_quotient (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hr V hVcard.ge
    (r := 2) (n := 7) (t := 3) (by intro k hk; omega)
  exact hk3.trans (CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num) A hA hAk)

end Rank

end CFSG.EvenSporadicStandard.Induction.Hyp
