module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5CovB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5F53
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5K1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CompOf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Tab5_cover_i4_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
        (Kind5 L s 3 ∨ Kind5 L s 4 ∨ Kind5 L s 5) →
          ∃ u ∈ XOut L s, orderOf u = 2 ∧ IsI4PlusIn L u ∧ s * u ∈ conjClassIn L s
  := by
  intro G _ _ L hL s hs2 hs hk
  rcases hk with h3 | h4 | h5
  · exact asc82Tab5_cover_i4_kind3_of hS G L hL s hs2 hs h3
  · exact asc82Tab5_cover_i4_kind4_of hS G L hL s hs2 hs h4
  · exact asc82Tab5_cover_i4_kind5_of hS G L hL s hs2 hs h5

theorem asc82Tab5_of (hS : Asc82SchurU43) (hM : Asc82Tab6M) (hX : Asc82Tab6MExcl) :
    Asc82Tab5 :=
  ⟨asc82Tab5_classify_of hM, asc82Tab5_excl_of hM hX, asc82Tab5_kind_ne_central_of,
    asc82Tab5_layer_trivial_of hM, asc82Tab5_pocket_kind_of hS, asc82Tab5_inner_lift_of hS,
    asc82Tab5_inv_classes_of hS, asc82Tab5_tz_not_pocket_of hS, asc82Tab5_f53_of hS,
    asc82Tab5_xout_eq_of hM, asc82Tab5_xout_i3_of hM, asc82Tab5_cover_i4_of hS,
    asc82Tab5_layer_i4m_of hS hM, asc82Tab5_i4m_inv_of hS, asc82Tab5_i4m_of_comp_of hS hM,
    asc82Tab5_prod_i4m_of hS⟩

end CFSG.OddStandard.SmallF3.Omega
