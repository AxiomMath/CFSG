module

public import CFSG.LargeExtraspecial.AS35YUHub
public import CFSG.LargeExtraspecial.AS35YN
public import CFSG.LargeExtraspecial.AS35YTComm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}


theorem false_of_odd_psl4_YU (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSL 4 2 1)
    (hdim : finrank (ZMod 2) (commU_YS S) = 2 * 3 + 1) {r : S.Qt} (hrW : r ∈ fixW_YS S)
    (hrU : r ∈ commU_YS S) (hr0 : r ≠ 0) : False := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  rcases AS35YU.fix_or_dim_six_of_psl4_YU (rootClass_EhatAsc_YN hS hst hnd)
      (a2Action_EhatAsc_YN hS hc) hL with hfix | hle
  · exact hr0 (hfix r (by rw [commSpaceOf_actHat_YT hc]; exact hrU) (actHat_fix_YT hc hrW))
  · rw [commSpaceOf_actHat_YT hc] at hle
    have hle' : finrank (ZMod 2) (commU_YS S) ≤ 6 := hle
    omega

theorem false_of_odd_pomega4_YU (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaPlus 4 2 1 ∨
      LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaMinus 4 2 1)
    (hdim : finrank (ZMod 2) (commU_YS S) = 2 * 4 + 1) : False := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  have hle := AS35YU.dim_le_eight_of_pomega4_YU (rootClass_EhatAsc_YN hS hst hnd)
    (a2Action_EhatAsc_YN hS hc) hL
  rw [commSpaceOf_actHat_YT hc] at hle
  have hle' : finrank (ZMod 2) (commU_YS S) ≤ 8 := hle
  omega

end Setting

end CFSG.LargeExtraspecial
