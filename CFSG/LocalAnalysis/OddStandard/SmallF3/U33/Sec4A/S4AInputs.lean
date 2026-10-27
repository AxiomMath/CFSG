module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxOfHyp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY13
public import CFSG.GH74.NoComponent

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G]


theorem Sec4Inputs.exists_normal_e8 (hI : Sec4Inputs) (hG : Sec4Glob G) {t : G}
    {L : Subgroup G} (h : Hyp G t L) (𝒮 : Sylow 2 G) :
    ∃ E : Subgroup G, E ≤ (𝒮 : Subgroup G) ∧ (E.subgroupOf (𝒮 : Subgroup G)).Normal ∧
      CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  by_cases hgen4 : GH74.Gen4 G
  ·
    exfalso
    have hnonab : ∃ a b : G, a * b ≠ b * a := by
      by_contra hcon
      push_neg at hcon
      haveI : IsSimpleGroup G := hG.simple
      letI : CommGroup G := { ‹Group G› with mul_comm := fun a b => hcon a b }
      have hprime : (Nat.card G).Prime := IsSimpleGroup.prime_card
      rcases hprime.eq_one_or_self_of_dvd (2 ^ 11) hG.dvd with h1 | h1
      · norm_num at h1
      · rw [← h1] at hprime
        norm_num at hprime
    have h2rank : 3 ≤ CFSG.Open.twoRank G := by
      obtain ⟨S, x₁, x₂, lam, rho, hctx⟩ := exists_ctx0_of_hyp h
      exact CFSG.OddStandard.SmallF3.FritzII.three_le_twoRank_of_ctx0 hctx
    have hconcl := hI.gh74 G hG.simple hnonab h2rank hgen4
    exact hG.not_catalog (CFSG.GH74.catalog_of_ghList hconcl.ghList)
  ·
    exact hI.corA G hgen4 𝒮

end CFSG.OddStandard.SmallF3.HarrisU33
