module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.ExcE6Sign
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.BlockSL

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit
open CFSG.ClassicalInvolution.RouteD (path6)
open scoped MatrixGroups


theorem hasCleanFullClassBMember_of_lieModel_e6
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q] (h : CFSG.Blueprint.LieModel Q .E6 0 3 1) :
    HasCleanFullClassBMember Q := by
  have hK3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  obtain ⟨α, hα, hαk⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover .E6 0 3 1
    Nat.prime_three (by norm_num) trivial ⟨Nat.prime_three, le_rfl, rfl⟩ Q h
  obtain ⟨Θ, hker, hrange, hblk⟩ := exists_theta_e6
  have hΘinj : Function.Injective Θ := theta_injective_e6 hker hblk
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz' : z ∈ Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
        (GaloisField 3 1)) := hαk hz
    rw [center_e6_three_eq_bot] at hz'
    exact Subgroup.mem_bot.1 hz'
  have hnorm := normal_range_theta_e6 hrange (e6Eps_theta_negOneSix hker hblk)
  exact hasCleanFullClassBMember_of_block α hα hαk Θ (hαinj.comp hΘinj)
    (orderOf_negOneSix CFSG.ClassicalInvolution.Q3.Q3W.two_ne_zero_gf3)
    (negOneSix_mem_center _) hnorm (blockData_specialLinear hGA hK3 (Or.inr rfl))

end CFSG.OddStandard.HigherRank.F3
