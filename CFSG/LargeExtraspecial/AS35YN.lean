module

public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.LargeExtraspecial.AS35XGen
public import CFSG.LargeExtraspecial.A2ModBasic
public import CFSG.LargeExtraspecial.AS35YLSCen
public import CFSG.LargeExtraspecial.S12InspPSLMain
public import CFSG.LargeExtraspecial.S12InspSpOSp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions

namespace AS35YN

theorem spOrd_le {a b : ℕ} (h : a ≤ b) :
    2 ^ (a ^ 2) * ∏ j ∈ Finset.Icc 1 a, (2 ^ (2 * j) - 1) ≤
      2 ^ (b ^ 2) * ∏ j ∈ Finset.Icc 1 b, (2 ^ (2 * j) - 1) := by
  refine Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left h 2)) ?_
  refine Finset.prod_le_prod_of_subset_of_one_le (Finset.Icc_subset_Icc_right h) ?_
  intro j hj _
  have h1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have h2 : 2 ≤ 2 ^ (2 * j) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ 2 * j))
  omega

theorem spOrd_pred_le_card_of_lieModel_POmega {X : Type} [Group X] {m : ℕ}
    (h : LieModel X .POmegaPlus m 2 1 ∨ LieModel X .POmegaMinus m 2 1) :
    2 ^ ((m - 1) ^ 2) * ∏ j ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * j) - 1) ≤ Nat.card X := by
  obtain ⟨hm, hX | hX⟩ := A2Mod.Ord.card_of_lieModel_POmega h
  all_goals
    have h2 : 2 ^ ((m - 1) ^ 2) ≤ 2 ^ (m * (m - 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [sq]; exact Nat.mul_le_mul_right _ (by omega))
    have h3 : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
  · rw [hX, A2Mod.Ord.ordD_two_eq (by omega)]
    exact Nat.mul_le_mul_right _ (le_trans h2 (Nat.le_mul_of_pos_right _ (by omega)))
  · rw [hX, A2Mod.Ord.ordTwistedD_two_eq (by omega)]
    exact Nat.mul_le_mul_right _ (le_trans h2 (Nat.le_mul_of_pos_right _ (by omega)))

end AS35YN

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

open AS35YL

theorem rootClass_EhatAsc_YN (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) :
    A2Mod.RootClass (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc := by
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := nontrivial_of_inspNondeg_YL hnd
  exact ⟨isTransClass34_EhatAsc_YL hS hst, hnd,
    AS35X.eq_bot_of_nilpotent hst.fitting_le_center _ inferInstance inferInstance,
    fun N hN hp => AS35X.eq_bot_of_nilpotent hst.fitting_le_center N hN hp.isNilpotent⟩

theorem a2Action_EhatAsc_YN (hS : S.SixHyp) (hc : center S.LbarAsc = ⊥) :
    A2Mod.A2Action S.EhatAsc S.q (actHat_YL hc) := by
  refine ⟨S.q_nondegenerate, actHat_YL_injective hc, actHat_YL_isometry hc, ?_⟩
  rintro _ ⟨l, hl, rfl⟩
  rw [actHat_YL_mk]
  exact isTypeA_of_mem_DbarAsc_YL hS hl

theorem card_quot_dvd_YN (hc : center S.LbarAsc = ⊥) :
    Nat.card (S.LbarAsc ⧸ center S.LbarAsc) ∣
      2 ^ (S.width ^ 2) * ∏ j ∈ Finset.Icc 1 S.width, (2 ^ (2 * j) - 1) := by
  rw [← S12DW.card_orthogonalGroup_mul_ncard_eq S.q_nondegenerate S.finrank_Qt_eq_two_mul_width]
  exact (Subgroup.card_dvd_of_injective _ (quotEmb_YL_injective _ hc)).mul_right _

theorem two_mul_card_quot_le_YN (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hc : center S.LbarAsc = ⊥) [Nontrivial (S.LbarAsc ⧸ center S.LbarAsc)] :
    2 * Nat.card (S.LbarAsc ⧸ center S.LbarAsc) ≤
      2 ^ (S.width ^ 2) * ∏ j ∈ Finset.Icc 1 S.width, (2 ^ (2 * j) - 1) := by
  obtain ⟨d, -, -, -, hdA⟩ := exists_inv_of_center_eq_bot_YL hS hst hc
  have hO : Nat.card S.O * {v | S.q v = 0}.ncard =
      2 ^ (S.width ^ 2) * ∏ j ∈ Finset.Icc 1 S.width, (2 ^ (2 * j) - 1) :=
    S12DW.card_orthogonalGroup_mul_ncard_eq S.q_nondegenerate S.finrank_Qt_eq_two_mul_width
  have hle := card_quot_le_card_O_YL hc
  have hZ : 2 ≤ {v | S.q v = 0}.ncard :=
    spo_two_le_ncard_sing (t := quotEmb_YL S.LbarAsc hc d) hdA
  rw [← hO]
  calc 2 * Nat.card (S.LbarAsc ⧸ center S.LbarAsc) ≤ 2 * Nat.card S.O := Nat.mul_le_mul_left _ hle
    _ = Nat.card S.O * 2 := mul_comm _ _
    _ ≤ Nat.card S.O * {v | S.q v = 0}.ncard := Nat.mul_le_mul_left _ hZ

theorem false_of_lieModel_PSL4_YN (hc : center S.LbarAsc = ⊥)
    (hw : S.width = 4) (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSL 4 2 1)
    (hirr : S.LbarIrred_YL) : False := by
  obtain ⟨φ⟩ := psl_nonempty_mulEquiv_sl_of_lieModel hL
  have hdim : finrank (ZMod 2) S.Qt = 8 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  set H := S.LbarAsc.map S.O.subtype
  have ψ : H ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    ((S.LbarAsc.equivMapOfInjective S.O.subtype (subtype_injective _)).symm.trans
      (quotEquiv_YL S.LbarAsc hc).symm).trans φ
  obtain ⟨W, hW0, hWt, hWH⟩ := SL4Mod.s12SL4ModuleInput S.Qt hdim H ⟨ψ⟩
  rcases hirr W (fun l hl w hw => hWH _ ⟨l, hl, rfl⟩ w hw) with h | h
  · exact hW0 h
  · exact hWt h

end Setting

end CFSG.LargeExtraspecial
