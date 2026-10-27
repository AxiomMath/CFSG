module

public import CFSG.LargeExtraspecial.AS35YN
public import CFSG.LargeExtraspecial.A2ModD4Defs
public import CFSG.LargeExtraspecial.A2ModNDefs
public import CFSG.LargeExtraspecial.AS35YLMLin
public import CFSG.LargeExtraspecial.AS35YLMOm
public import CFSG.LargeExtraspecial.AS35YLSFam
public import CFSG.LargeExtraspecial.AS35YLSU33

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions

namespace S14

theorem asc512InspPSL_ofN (hPSL : S12PSLModuleInputN)
    (h5127 : Asc512FiveTwelveSevenStmt) (hfix : Asc512FixFreeStmt)
    (h43 : Asc512PSL4WidthThreeStmt) : Asc512InspFor Asc512PSLFam := by
  intro G _ _ S hS hst h
  have hfixS := hfix G S hS hst (Or.inl h)
  obtain ⟨hnd, m, hm, hL⟩ := h
  by_cases hm4 : 4 ≤ m
  · exfalso
    have hirrS := Setting.lbarIrred_of_fixFree_YL hS hst hnd h5127 hfixS
    have hc := Setting.center_LbarAsc_eq_bot_YL hS hst hnd
    have hdim := hPSL _ m hm4 hL _ (Setting.rootClass_EhatAsc_YN hS hst hnd) S.Qt S.q
      (Setting.actHat_YL hc) (Setting.a2Action_EhatAsc_YN hS hc) (Setting.irred_actHat_YL hc hirrS)
    rw [S.finrank_Qt_eq_two_mul_width] at hdim
    have h3 := hS.three_le_width
    have hw : S.width = 3 ∨ S.width = 4 := by omega
    obtain rfl : m = 4 := by
      by_contra hne
      have h31 : 31 ∣ Nat.card (S.LbarAsc ⧸ center S.LbarAsc) := by
        rw [(A2Mod.Ord.card_of_lieModel_PSL hL).2]
        exact A2Mod.Ord.dvd_ordA_two (a := 5) (by norm_num) (by omega) (by norm_num)
      have hdvd := h31.trans (Setting.card_quot_dvd_YN hc)
      rcases hw with hw | hw <;> rw [hw] at hdvd <;> revert hdvd <;> decide
    rcases hw with hw | hw
    · exact h43 G S hS hst hnd hL hirrS hw
    · exact Setting.false_of_lieModel_PSL4_YN hc hw hL hirrS
  · obtain rfl : m = 3 := by omega
    exact asc512InspPSL3_of h5127 G S hS hst ⟨hnd, hL⟩

theorem asc512InspPSp_ofN (hSp : S12SpModuleInputN) (h5127 : Asc512FiveTwelveSevenStmt)
    (hfix : Asc512FixFreeStmt) : Asc512InspFor Asc512PSpFam := by
  intro G _ _ S hS hst h
  have hfixS := hfix G S hS hst (Or.inr (Or.inl h))
  obtain ⟨hnd, m, hm, hL⟩ := h
  have hirrS := Setting.lbarIrred_of_fixFree_YL hS hst hnd h5127 hfixS
  have hc := Setting.center_LbarAsc_eq_bot_YL hS hst hnd
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  have hdim := hSp _ m hm hL _ (Setting.rootClass_EhatAsc_YN hS hst hnd) S.Qt S.q
    (Setting.actHat_YL hc) (Setting.a2Action_EhatAsc_YN hS hc) (Setting.irred_actHat_YL hc hirrS)
  rw [S.finrank_Qt_eq_two_mul_width] at hdim
  have h2X := Setting.two_mul_card_quot_le_YN hS hst hc
  have hlt : m < S.width := by
    by_contra hge
    have hle := AS35YN.spOrd_le (not_lt.mp hge)
    rw [← S12InspSpO.card_of_lieModel_psp hL] at hle
    have hpos : 0 < Nat.card (S.LbarAsc ⧸ center S.LbarAsc) := Nat.card_pos
    omega
  obtain rfl : m = 3 := by omega
  exact Or.inr ⟨by omega, hL⟩

theorem asc512InspPOmega_ofN (hO : S12OmegaModuleInputN) (h5127 : Asc512FiveTwelveSevenStmt)
    (hfix : Asc512FixFreeStmt) (hnat : Asc512POmegaNatStmt) :
    Asc512InspFor Asc512POmegaFam := by
  intro G _ _ S hS hst h
  exfalso
  have hfixS := hfix G S hS hst (Or.inr (Or.inr (Or.inl h)))
  obtain ⟨hnd, m, hm, hL⟩ := h
  have hirrS := Setting.lbarIrred_of_fixFree_YL hS hst hnd h5127 hfixS
  have hc := Setting.center_LbarAsc_eq_bot_YL hS hst hnd
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  have hdim := hO _ m hm hL _ (Setting.rootClass_EhatAsc_YN hS hst hnd) S.Qt S.q
    (Setting.actHat_YL hc) (Setting.a2Action_EhatAsc_YN hS hc) (Setting.irred_actHat_YL hc hirrS)
  rw [S.finrank_Qt_eq_two_mul_width] at hdim
  have hw : S.width = m := by
    rcases hdim with hlt | heq
    · have h2X := Setting.two_mul_card_quot_le_YN hS hst hc
      have hle : m ≤ S.width := by
        by_contra hgt
        have h1 := AS35YN.spOrd_le (show S.width ≤ m - 1 by omega)
        have h2 := AS35YN.spOrd_pred_le_card_of_lieModel_POmega hL
        have hpos : 0 < Nat.card (S.LbarAsc ⧸ center S.LbarAsc) := Nat.card_pos
        omega
      omega
    · omega
  rw [← hw] at hL
  exact hnat G S hS hst hnd hL hirrS

theorem asc512InspExc_ofN (hD4 : DW.DW2ModuleInputD4) (hM : S12ExcModuleInputN) :
    Asc512InspFor Asc512ExcFam := by
  intro G _ _ S hS hst h
  exfalso
  obtain ⟨hnd, τ, hτ, hX⟩ := h
  have hc := Setting.center_LbarAsc_eq_bot_YL hS hst hnd
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  have hR := Setting.rootClass_EhatAsc_YN hS hst hnd
  have hA := Setting.a2Action_EhatAsc_YN hS hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨d, -, hd1, hdd, hdA⟩ := Setting.exists_inv_of_center_eq_bot_YL hS hst hc
    have h3 := hD4 _ hX S.Qt (Setting.actHat_YL hc) (Setting.actHat_YL_injective hc) d hd1 hdd
    have h2 := hdA.2.2.2.1
    omega
  · exact hM _ .F4 (by decide) hX _ hR S.Qt S.q _ hA
  · exact hM _ .E6 (by decide) hX _ hR S.Qt S.q _ hA
  · exact hM _ .twistedE6 (by decide) hX _ hR S.Qt S.q _ hA
  · exact hM _ .E7 (by decide) hX _ hR S.Qt S.q _ hA
  · exact hM _ .E8 (by decide) hX _ hR S.Qt S.q _ hA

theorem asc512InspNondeg_ofN'
    (hF : DW.DW2FieldInput) (hPSL : S12PSLModuleInputN)
    (hSp : S12SpModuleInputN) (hO : S12OmegaModuleInputN) (hM : S12ExcModuleInputN)
    (hD4 : DW.DW2ModuleInputD4) (h5127 : Asc512FiveTwelveSevenStmt) (hfix : Asc512FixFreeStmt)
    (h43 : Asc512PSL4WidthThreeStmt) (hnat : Asc512POmegaNatStmt)
    (hU33 : Asc512U33ModuleInput) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) =>
      InspNondeg X D ∧ CFSG.Timmesfeld.Outcome X :=
  asc512InspNondeg_of_families (asc512InspField_of hF) (asc512InspPSL_ofN hPSL h5127 hfix h43)
    (asc512InspPSp_ofN hSp h5127 hfix) (asc512InspPOmega_ofN hO h5127 hfix hnat)
    (asc512InspExc_ofN hD4 hM) (asc512InspU33_of hU33 h5127 hfix) asc512InspAlt6 asc512InspJ2

end S14

end CFSG.LargeExtraspecial
