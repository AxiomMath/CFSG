module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Bender

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open CFSG.GH74.Uniqueness.Bender

theorem ivk93_l28 :
    Ivk93Empty (fun X _ => LieModel X .PSL 2 2 3) := by
  refine ivk93_empty_of_cfg fun J _ _ hJ x _ q L₁ L₂ hc => ?_
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := J) (f := 3) (by norm_num) hJ
  have hB : BenderType J 3 1 1 := .linear 3 (by norm_num) e
  have hcard := bender_card_centralizer_involution hB hc.mul_self_eq_one hc.ne_one
  exact hc.false_of_card_cent_dvd (N := 8) (by rw [hcard]; norm_num)
    (not_sl2_dvd_of_lt (by norm_num) (by norm_num))

theorem ivk93_l216 :
    Ivk93Empty (fun X _ => LieModel X .PSL 2 2 4) := by
  refine ivk93_empty_of_cfg fun J _ _ hJ x _ q L₁ L₂ hc => ?_
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := J) (f := 4) (by norm_num) hJ
  have hB : BenderType J 4 1 1 := .linear 4 (by norm_num) e
  have hcard := bender_card_centralizer_involution hB hc.mul_self_eq_one hc.ne_one
  exact hc.false_of_card_cent_dvd (N := 16) (by rw [hcard]; norm_num)
    (not_sl2_dvd_of_lt (by norm_num) (by norm_num))

theorem ivk93_u34 :
    Ivk93Empty (fun X _ => LieModel X .PSU 3 2 2) := by
  refine ivk93_empty_of_cfg fun J _ _ hJ x _ q L₁ L₂ hc => ?_
  have hS := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  obtain ⟨e⟩ := (RankTwoShapes.statedClassicalModel_PSU_three_two_iff J 2 le_rfl).1 hS
  have hB : BenderType J 2 3 _ := .unitary 2 le_rfl e
  have hcard := bender_card_centralizer_involution hB hc.mul_self_eq_one hc.ne_one
  have h320 : Nat.card ↥(centralizer ({x} : Set J)) = 320 := by
    rw [hcard]
    norm_num
  exact hc.false_of_card_cent_dvd (N := 320) (by rw [h320])
    (fun q _ => not_sl2_dvd_of_not_three (by norm_num) q)

theorem ivk93_sz8 :
    Ivk93Empty (fun X _ => LieModel X .twistedB2 0 2 3) := by
  refine ivk93_empty_of_cfg fun J _ _ hJ x _ q L₁ L₂ hc => ?_
  obtain ⟨e⟩ := KGroups.Sz8.equiv_of_lieModel hJ
  have hcard : Nat.card J = 29120 := by
    rw [Nat.card_congr e.toEquiv, KGroups.card_group KGroups.Sz8.QP KGroups.Sz8.QP_ok,
      KGroups.Sz8.QP_valid.2]
  exact hc.false_of_card_group (N := 29120) (by rw [hcard])
    (fun q _ => not_sl2_dvd_of_not_three (by norm_num) q)

end CFSG.GH74.GLS.IVK.Proofs2
