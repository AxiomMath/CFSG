module

public import CFSG.LargeExtraspecial.AS35YTCaseA
public import CFSG.LargeExtraspecial.A2ModNDefs
public import CFSG.LargeExtraspecial.AS35YN

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem psl_dim_YT (hPSL : S12PSLModuleInputN) (hS : S.SixHyp)
    (hst : S.Asc512Standing) (h5127 : S14.Asc512FiveTwelveSevenStmt)
    (hnd : InspNondeg _ S.EhatAsc) {m : ℕ} (hm : 4 ≤ m)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSL m 2 1) (h : RadSing_YS S) :
    m = 4 ∧ finrank (ZMod 2) (V0_YS S) = 6 := by
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  have hA := a2Action_V0_YT hS hst hc h
  have hirr := irred_rhoX_YT hS hst hnd hc h5127 h
  have hdim := hPSL _ m hm hL _ (rootClass_EhatAsc_YN hS hst hnd) (V0_YS S) (q0_YS h)
    (rhoX_YS hst hc) hA hirr
  obtain ⟨k, hk⟩ := AS35YT.exists_finrank_eq_two_mul (q0_YS_nondegenerate h)
  have hdvd := AS35YT.card_dvd_spOrd (q0_YS_nondegenerate h) hk (rhoX_YS hst hc) hA.2.1
    hA.2.2.1
  have hk4 : k ≤ 4 := by omega
  obtain rfl : m = 4 := by
    by_contra hne
    have h31 : 31 ∣ Nat.card (S.LbarAsc ⧸ center S.LbarAsc) := by
      rw [(A2Mod.Ord.card_of_lieModel_PSL hL).2]
      exact A2Mod.Ord.dvd_ordA_two (a := 5) (by norm_num) (by omega) (by norm_num)
    have h' := h31.trans hdvd
    interval_cases k <;> revert h' <;> decide
  have hX : Nat.card (S.LbarAsc ⧸ center S.LbarAsc) = 20160 := by
    rw [(A2Mod.Ord.card_of_lieModel_PSL hL).2]
    decide
  rw [hX] at hdvd
  have hk34 : k = 3 ∨ k = 4 := by
    interval_cases k <;> first | (left; rfl) | (right; rfl) | (revert hdvd; decide)
  rcases hk34 with rfl | rfl
  · exact ⟨rfl, by omega⟩
  · exfalso
    obtain ⟨φ⟩ := psl_nonempty_mulEquiv_sl_of_lieModel hL
    have ψ : (rhoX_YS hst hc).range ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
      (MonoidHom.ofInjective hA.2.1).symm.trans φ
    obtain ⟨W, hW0, hWt, hWH⟩ := SL4Mod.s12SL4ModuleInput (V0_YS S) (by omega) _ ⟨ψ⟩
    rcases hirr W (fun x w hw => hWH _ ⟨x, rfl⟩ w hw) with h' | h'
    · exact hW0 h'
    · exact hWt h'

theorem psp_dim_YT (hSp : S12SpModuleInputN) (hS : S.SixHyp) (hst : S.Asc512Standing)
    (h5127 : S14.Asc512FiveTwelveSevenStmt)
    (hfam : S14.Asc512PSpFam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc) (h : RadSing_YS S) :
    LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSp 3 2 1 ∧ finrank (ZMod 2) (V0_YS S) = 8 := by
  obtain ⟨hnd, m, hm, hL⟩ := hfam
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  have hA := a2Action_V0_YT hS hst hc h
  have hirr := irred_rhoX_YT hS hst hnd hc h5127 h
  have hdim := hSp _ m hm hL _ (rootClass_EhatAsc_YN hS hst hnd) (V0_YS S) (q0_YS h)
    (rhoX_YS hst hc) hA hirr
  obtain ⟨k, hk⟩ := AS35YT.exists_finrank_eq_two_mul (q0_YS_nondegenerate h)
  obtain ⟨v, hv0, hqv⟩ := exists_sing_V0_YT hS hst hnd h
  have h2 := AS35YT.two_mul_card_le_spOrd (q0_YS_nondegenerate h) hk (rhoX_YS hst hc) hA.2.1
    hA.2.2.1 hv0 hqv
  have hlt : m < k := by
    by_contra hge
    have hle := AS35YN.spOrd_le (not_lt.mp hge)
    rw [← S12InspSpO.card_of_lieModel_psp hL] at hle
    have hpos : 0 < Nat.card (S.LbarAsc ⧸ center S.LbarAsc) := Nat.card_pos
    omega
  obtain rfl : m = 3 := by omega
  exact ⟨hL, by omega⟩

theorem pomega_dim_YT (hO : S12OmegaModuleInputN) (hS : S.SixHyp) (hst : S.Asc512Standing)
    (h5127 : S14.Asc512FiveTwelveSevenStmt) (hnd : InspNondeg _ S.EhatAsc) {m : ℕ} (hm : 4 ≤ m)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaPlus m 2 1 ∨
      LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaMinus m 2 1) (h : RadSing_YS S) :
    finrank (ZMod 2) (V0_YS S) = 2 * m := by
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  have hA := a2Action_V0_YT hS hst hc h
  have hirr := irred_rhoX_YT hS hst hnd hc h5127 h
  rcases hO _ m hm hL _ (rootClass_EhatAsc_YN hS hst hnd) (V0_YS S) (q0_YS h)
    (rhoX_YS hst hc) hA hirr with hlt | heq
  · obtain ⟨k, hk⟩ := AS35YT.exists_finrank_eq_two_mul (q0_YS_nondegenerate h)
    obtain ⟨v, hv0, hqv⟩ := exists_sing_V0_YT hS hst hnd h
    have h2 := AS35YT.two_mul_card_le_spOrd (q0_YS_nondegenerate h) hk (rhoX_YS hst hc) hA.2.1
      hA.2.2.1 hv0 hqv
    have hle : m ≤ k := by
      by_contra hgt
      have h1 := AS35YN.spOrd_le (show k ≤ m - 1 by omega)
      have h3 := AS35YN.spOrd_pred_le_card_of_lieModel_POmega hL
      have hpos : 0 < Nat.card (S.LbarAsc ⧸ center S.LbarAsc) := Nat.card_pos
      omega
    omega
  · exact heq

end Setting

end CFSG.LargeExtraspecial
