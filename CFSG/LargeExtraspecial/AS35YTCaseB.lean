module

public import CFSG.LargeExtraspecial.AS35YTComm
public import CFSG.LargeExtraspecial.AS35YTSpOrd
public import CFSG.LargeExtraspecial.AS35YTHubO
public import CFSG.LargeExtraspecial.AS35YTHubL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem card_quot_eq_YT (hc : center S.LbarAsc = ⊥) :
    Nat.card (S.LbarAsc ⧸ center S.LbarAsc) = Nat.card S.LbarAsc :=
  Nat.card_congr (AS35YL.quotEquiv_YL S.LbarAsc hc).toEquiv

theorem ne_zero_of_q_ne_zero_YT {v : S.Qt} (hv : S.q v ≠ 0) : v ≠ 0 := fun h =>
  hv (by rw [h, QuadraticMap.map_zero])


theorem radSing_of_psl_YT (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) {k : ℕ} (hk : 5 ≤ k)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSL k 2 1) : RadSing_YS S := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  intro v hvW hvperp
  have hvU : v ∈ commU_YS S := mem_commU_YS.mpr hvperp
  rw [AS35YT.fix_eq_zero_of_psl (rootClass_EhatAsc_YN hS hst hnd) (a2Action_EhatAsc_YN hS hc) hk
    hL (by rw [commSpaceOf_actHat_YT hc]; exact hvU) (actHat_fix_YT hc hvW), QuadraticMap.map_zero]

theorem radSing_of_pomega_YT (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) {k : ℕ} (hk : 5 ≤ k)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaPlus k 2 1 ∨
      LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaMinus k 2 1) : RadSing_YS S := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  intro v hvW hvperp
  by_contra hqv
  obtain ⟨j, -, hjU, hcard, -⟩ :=
    caseB_YT hst hvW (mem_commU_YS.mpr hvperp) (ne_zero_of_q_ne_zero_YT hqv)
  have hdim := (AS35YT.dim_of_pomega (rootClass_EhatAsc_YN hS hst hnd)
    (a2Action_EhatAsc_YN hS hc) hL).1 hk
  rw [commSpaceOf_actHat_YT hc] at hdim
  have hdim' : finrank (ZMod 2) (commU_YS S) = 2 * k := hdim
  have hkj := AS35YT.le_of_le_spOrd_of_POmega hL (by rw [card_quot_eq_YT hc]; exact hcard)
  omega

theorem odd_of_psl4_YT (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSL 4 2 1) {r : S.Qt} (hrW : r ∈ fixW_YS S)
    (hrU : r ∈ commU_YS S) (hr : S.q r ≠ 0) :
    finrank (ZMod 2) (commU_YS S) = 2 * 3 + 1 ∧
      ∀ v ∈ fixW_YS S, v ∈ commU_YS S → v = 0 ∨ v = r := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨j, -, hjU, hcard, hR⟩ := caseB_YT hst hrW hrU (ne_zero_of_q_ne_zero_YT hr)
  rcases AS35YT.fix_or_dim_of_psl4 (rootClass_EhatAsc_YN hS hst hnd) (a2Action_EhatAsc_YN hS hc)
      hL with hfix | hle
  · exact absurd (hfix r (by rw [commSpaceOf_actHat_YT hc]; exact hrU) (actHat_fix_YT hc hrW))
      (ne_zero_of_q_ne_zero_YT hr)
  · rw [commSpaceOf_actHat_YT hc] at hle
    have hle' : finrank (ZMod 2) (commU_YS S) ≤ 7 := hle
    have hj := AS35YT.three_le_of_le_spOrd_of_PSL4 hL (by rw [card_quot_eq_YT hc]; exact hcard)
    have heq : 2 * j + 1 = finrank (ZMod 2) (commU_YS S) := by omega
    exact ⟨by omega, hR heq⟩

theorem odd_of_pomega4_YT (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaPlus 4 2 1 ∨
      LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaMinus 4 2 1) {r : S.Qt}
    (hrW : r ∈ fixW_YS S) (hrU : r ∈ commU_YS S) (hr : S.q r ≠ 0) :
    finrank (ZMod 2) (commU_YS S) = 2 * 4 + 1 ∧
      ∀ v ∈ fixW_YS S, v ∈ commU_YS S → v = 0 ∨ v = r := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨j, -, hjU, hcard, hR⟩ := caseB_YT hst hrW hrU (ne_zero_of_q_ne_zero_YT hr)
  have hle := (AS35YT.dim_of_pomega (rootClass_EhatAsc_YN hS hst hnd)
    (a2Action_EhatAsc_YN hS hc) hL).2 rfl
  rw [commSpaceOf_actHat_YT hc] at hle
  have hle' : finrank (ZMod 2) (commU_YS S) ≤ 9 := hle
  have hj := AS35YT.le_of_le_spOrd_of_POmega hL (by rw [card_quot_eq_YT hc]; exact hcard)
  have heq : 2 * j + 1 = finrank (ZMod 2) (commU_YS S) := by omega
  exact ⟨by omega, hR heq⟩

theorem odd_of_psp_YT (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    {m : ℕ} (hm : 4 ≤ m) (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSp m 2 1) {r : S.Qt}
    (hrW : r ∈ fixW_YS S) (hrU : r ∈ commU_YS S) (hr : S.q r ≠ 0) :
    finrank (ZMod 2) (commU_YS S) = 2 * m + 1 ∧
      ∀ v ∈ fixW_YS S, v ∈ commU_YS S → v = 0 ∨ v = r := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨j, -, hjU, hcard, hR⟩ := caseB_YT hst hrW hrU (ne_zero_of_q_ne_zero_YT hr)
  have hle := (AS35YT.dim_of_psp (rootClass_EhatAsc_YN hS hst hnd)
    (a2Action_EhatAsc_YN hS hc) hL).1
  rw [commSpaceOf_actHat_YT hc] at hle
  have hle' : finrank (ZMod 2) (commU_YS S) ≤ max (2 * m + 1) 9 := hle
  rw [max_eq_left (by omega)] at hle'
  have hj := AS35YT.le_of_le_spOrd_of_PSp hL (by rw [card_quot_eq_YT hc]; exact hcard)
  have heq : 2 * j + 1 = finrank (ZMod 2) (commU_YS S) := by omega
  exact ⟨by omega, hR heq⟩

end Setting

end CFSG.LargeExtraspecial
