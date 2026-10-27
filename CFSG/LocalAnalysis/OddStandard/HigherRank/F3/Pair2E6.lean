module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Pair2E6Sign
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Pair2E6Normal
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Pair2E6Unitary

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit
open CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.ClassicalInvolution.RouteD (path6)
open scoped MatrixGroups


theorem hasCleanFullClassBMember_of_lieModel_twistedE6
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q] (h : CFSG.Blueprint.LieModel Q .twistedE6 0 3 1) :
    HasCleanFullClassBMember Q := by
  have hk : Nat.card (GaloisField 3 (2 * 1)) = 9 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hF : ringChar (GaloisField 3 (2 * 1)) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 (2 * 1)) 3]
    norm_num
  obtain ⟨α, hα, hαk⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover .twistedE6 0 3 1
    Nat.prime_three (by norm_num) trivial ⟨Nat.prime_three, le_rfl, rfl⟩ Q h
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz' := hαk hz
    rw [CFSG.ClassicalInvolution.Q3.exc3_center_twistedE6_model Nat.prime_three] at hz'
    exact Subgroup.mem_bot.1 hz'
  have hθ : ∀ c, frobQ 3 1 (frobQ 3 1 c) = c := frobQ_frobQ 3 1 le_rfl
  obtain ⟨Θ, hΘ⟩ := exists_theta6 (k := GaloisField 3 (2 * 1))
  have hσ := sigma_comp_theta6 (frobQ 3 1) hθ hΘ
  have hε := e6Isogeny_injective_of_card_nine hk
  have hΘinj : Function.Injective Θ := theta6_injective hk hF hε hΘ
  have hrange := range_theta6 hΘ
  have hfix : sigma (GaloisField 3 (2 * 1)) (frobQ 3 1) (Θ (negOneSix (GaloisField 3 (2 * 1)))) =
      Θ (negOneSix (GaloisField 3 (2 * 1))) := by
    have h1 := DFunLike.congr_fun hσ (negOneSix (GaloisField 3 (2 * 1)))
    have h2 := negOneSix_mem_unitaryGroup6 (k := GaloisField 3 (2 * 1)) (frobQ 3 1) hθ
    rw [mem_unitaryGroup6] at h2
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h2] using h1
  have hnormΘ := normal_range_theta6 hF hε hrange (e6EpsK_theta_negOneSix hF hε hΘ)
  have hnorm := normal_range_fixedRestrict _ _ Θ hσ hΘinj hfix hnormΘ
  have hX := blockData_unitaryGroup6 hGA hk (frobQ 3 1) hθ (frobQ_apply 3 1)
  refine hasCleanFullClassBMember_of_block α hα hαk (thetaFixed (frobQ 3 1) hθ Θ hσ)
    (hαinj.comp (thetaFixed_injective (frobQ 3 1) hθ hσ hΘinj))
    (c := ⟨negOneSix (GaloisField 3 (2 * 1)),
      negOneSix_mem_unitaryGroup6 (frobQ 3 1) hθ⟩) ?_ ?_ hnorm hX
  · rw [Subgroup.orderOf_mk]
    exact orderOf_negOneSix (Ring.two_ne_zero hF)
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (negOneSix_mem_center _) g.1)

end CFSG.OddStandard.HigherRank.F3
