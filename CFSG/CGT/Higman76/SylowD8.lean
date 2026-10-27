module

import CFSG.CGT.Higman76.Quotient
import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Core
public import CFSG.Open.LocalVocabulary

public section


namespace CFSG.CGT.Higman76

open Subgroup CFSG.Open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G] [Finite G]

theorem sylow_dihedral (S : Sylow 2 G) {a : G} (ha : orderOf a = 2) (haS : a ∈ S)
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤)
    (h2 : {x | x ∈ S ∧ IsConj a x}.ncard = 2) :
    Nonempty (S ≃* DihedralGroup 4) := by
  classical
  obtain ⟨b, hne_ba, hbS, hab, hb, hcl⟩ := exists_conj_pair S ha haS h2
  have hne : a ≠ b := hne_ba.symm
  have ha2 : a * a = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two ha).symm
  have hb2 : b * b = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two hb).symm
  have ha1 : a ≠ 1 := by intro h; rw [h] at ha; simp at ha
  have hb1 : b ≠ 1 := by intro h; rw [h] at hb; simp at hb
  have hcomm : a * b = b * a := mul_comm_of_conj_pair S hb haS hbS hne hcl
  obtain ⟨-, -, hzconj, hzord⟩ := mul_not_conj S ha hb haS hbS hne hcomm hcl
  have hVleS : fourGroup a b ≤ (S : Subgroup G) := fourGroup_le haS hbS
  have hcardV : Nat.card (fourGroup a b) = 4 := fourGroup_card ha2 hb2 hcomm ha1 hb1 hne
  have hVea : IsElemAbelian 2 (fourGroup a b) := fourGroup_isElemAbelian ha2 hb2 hcomm
  have hweak := fourGroup_weakly_closed S hab hcl
  have hgenV : Subgroup.normalClosure (fourGroup a b : Set G) = ⊤ :=
    normalClosure_fourGroup_eq_top hgen
  have h33 := hallFusionThm32 G (S : Subgroup G) (fourGroup a b)
    (isSylowOf_coe_sylow S) hVleS hcardV hVea hweak
  rcases h33 with hcase1 | hcase2 | hcase3
  · rw [hgenV] at hcase1
    exact (not_sylowOf_fourGroup S ha hb haS hbS hne hab hcl hcase1).elim
  · exact (not_quotient_psu3 S ha hzord hzconj hgen hcase2).elim
  · rw [hgenV] at hcase3
    exact hcase3 (S : Subgroup G) (isSylowOf_coe_sylow S)

end CFSG.CGT.Higman76
