module

public import CFSG.LargeExtraspecial.AS35YSWInv
public import CFSG.LargeExtraspecial.AS35YSDefs
public import CFSG.LargeExtraspecial.AS35YSIrr
public import CFSG.LargeExtraspecial.AS35YSWCent
public import CFSG.LargeExtraspecial.AS35YSWClose

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_u33_YSW
    (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hU : S14.Asc512U33Fam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc) : False := by
  by_cases hrad : RadSing_YS S
  · exact false_of_u33_YS S14.asc512U33ModuleInput hS hst S14.asc512FiveTwelveSevenStmt hU hrad
  obtain ⟨hnd, hL⟩ := hU
  simp only [RadSing_YS, not_forall] at hrad
  obtain ⟨v, hvW, hvperp, hqv⟩ := hrad
  have hqv1 : S.q v = 1 := (AS35YR.Frame.zmod2_cases_YR _).resolve_left hqv
  have hv0 : v ≠ 0 := fun h => by rw [h, QuadraticMap.map_zero] at hqv1; exact zero_ne_one hqv1
  have h4 := width_eq_four_of_u33_YS hS hst hnd hL
  obtain ⟨x, hxL, hx7, hx1⟩ := exists_seven_u33_YS hS hst hnd hL
  have hW := fixW_le_span_YS h4 hxL hx7 hx1 hvW hvperp hv0
  have hCg : ∀ c ∈ S.Mbar ⊓ centralizer S.DbarAsc, c = 1 := fun c hc =>
    cg_trivial_YS hS hst h4 hxL hx7 hx1 hqv1 hvW hW hc
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨ι, hι, hιA, hιL, hιP⟩ := exists_iota_YS hst hc hL hCg
  have hM := card_mbar_le_YS ι hι hιA
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  obtain ⟨bb, hbX, hbD, hbt⟩ := exists_dbar_mem_pbar_YS hS hst hnd hL h4 hM ht htM
  have hbb : bb * bb = 1 := mul_self_of_mem_DbarAsc_YL hbD
  have hb1 : bb ≠ 1 := fun h => (isTypeA_of_mem_DbarAsc_YL hS hbD).2.1 (by rw [h]; rfl)
  have hR := fun U hUM hU2 hbU hUn => AS35YS.le_zpowers_of_model LbarAsc_le_Mbar_YL ι hι hιA
    hιL hιP (mem_inf.mp hbX).1 hbb hb1 U hUM hU2 hbU hUn
  obtain ⟨b, hb, hbM, rfl⟩ := hbD
  exact false_of_dbar_mem_pbar_YS hS ht htM hb hbM (mem_inf.mp hbX).2 hbt hR

end Setting

namespace S14

theorem asc512U33FixNonsingStmt_proof :
    Asc512U33FixNonsingStmt :=
  fun _ _ _ _ hS hst hU _ _ _ _ => (Setting.false_of_u33_YSW hS hst hU).elim

end S14

end CFSG.LargeExtraspecial
