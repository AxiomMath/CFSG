module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

private theorem gamma_fourA_setup (H : GammaHyps a z) {y zz b : G}
    (hy : y ∈ orb4A a z a) (hzz : zz = (a * y) ^ 2) (hb : b = zz * y) :
    IsConj a b ∧ b * y = zz ∧ y * b = zz ∧ IsConj a (y * zz) ∧ y * zz = zz * y ∧
      y * zz = b ∧ orderOf (a * y) = 4 := by
  have hyA : IsConj a y := hy.1
  have ha2 : a ^ 2 = 1 := H.sq_a (IsConj.refl a)
  have hy2 : y ^ 2 = 1 := H.sq_a hyA
  have hy2' : y * y = 1 := H.mul_self_a hyA
  have hord : orderOf (a * y) = 4 := tableV_orderOf_orb4A H.h hy
  obtain ⟨-, hyy, -, hcc⟩ :=
    tableV_dihedral ha2 hy2 hyA (m := 2) (by rw [hord])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hord⟩
  · rw [hb, hzz, ← hyy]
    exact hcc
  · rw [hb, hzz, mul_assoc, hy2', mul_one]
  · rw [hb, hzz, ← mul_assoc, hyy, mul_assoc, hy2', mul_one]
  · rw [hzz]
    exact hcc
  · rw [hzz]
    exact hyy
  · rw [hb, hzz]
    exact hyy

theorem gamma_fourA_row4A (H : GammaHyps a z) {y t : G} (hy : y ∈ orb4A a z a)
    (ht : t ∈ orb2A a y) (htb : t ∈ orb4A a z ((a * y) ^ 2 * y)) :
    ∃ c : G, c ∈ Qz ((a * y) ^ 2) ∧ c * y = y * c ∧ c * t = t * c ∧ orderOf c = 2 ∧
      orderOf (c * y) = 2 := by
  let zz : G := (a * y) ^ 2
  let b : G := zz * y
  obtain ⟨hbA, hb_mul_y, hy_mul_b, hyzz, _, hyzz_eq_b, _⟩ :=
    gamma_fourA_setup (zz := zz) (b := b) H hy rfl rfl
  have hyA : IsConj a y := hy.1
  have hzzZ : IsConj z zz := hy.2
  have htA : IsConj a t := ht.1
  have hyt : y * t = t * y := H.comm_of_orb2A hyA ht
  have hb_comm_y : b * y = y * b := by rw [hb_mul_y, hy_mul_b]
  have htb_a : t ∈ orb4A a z b := htb
  have htf5 : IsF5Type b z := isF5Type_of_isConj H.h hbA (IsConj.refl z)
  have htb' : t ∈ orb4A b z b := (gamma_orb4A_eq hbA z b).symm ▸ htb_a
  have hbt_ord : orderOf (b * t) = 4 := tableV_orderOf_orb4A htf5 htb'
  obtain ⟨hbc, htc, -, -⟩ :=
    tableV_dihedral (H.sq_a hbA) (H.sq_a htA) (hbA.symm.trans htA) (m := 2)
      (by rw [hbt_ord])
  let c : G := (b * t) ^ 2
  have hcZ : IsConj z c := htb.2
  have hc2 : orderOf c = 2 := H.orderOf_z hcZ
  have hyb_comm : Commute y b := hb_comm_y.symm
  have hbt_comm : Commute y (b * t) := hyb_comm.mul_right hyt
  have hy_comm_c : y * c = c * y := hbt_comm.pow_right 2
  have hcy : c * y = y * c := hy_comm_c.symm
  have hczz : c * zz = zz * c := by
    have hcb : Commute c b := hbc.symm
    have h3 : Commute c (b * y) := hcb.mul_right hcy
    rwa [hb_mul_y] at h3
  have hy_2Bb : y ∈ orb2B b z b := by
    rw [gamma_orb2B_eq hbA z b]
    exact ⟨hyA, by rw [hb_mul_y]; exact hzzZ⟩
  have hy_2At : y ∈ orb2A b t := by
    rw [gamma_orb2A_eq hbA t]
    exact ⟨hyA, by rw [← hyt]; exact ht.2⟩
  have hfig :=
    (H.hLines b z hbA (IsConj.refl z)).fig14_b t htb' y ⟨hy_2Bb, hy_2At⟩
  have hcyA : IsConj a (c * y) := hbA.trans hfig.1
  have hcy2 : orderOf (c * y) = 2 := H.orderOf_a hcyA
  have hy_Q : y ∈ Qz zz :=
    ((H.hF3 y z hyA (IsConj.refl z)).shape_2AB zz
      ⟨hzzZ, (gamma_isConj_iff hyA (y * zz)).mpr hyzz⟩).2
  have hxcyc : IsConj a (y * c) := by
    rw [← hcy]
    exact hcyA
  have hyczz_eq : (y * c) * zz = b * c := by
    rw [mul_assoc, hczz, ← mul_assoc, hyzz_eq_b]
  have hxcyc_zz : IsConj a ((y * c) * zz) := by
    rw [hyczz_eq]
    exact hbA.trans hfig.2.2.2.1
  have hyc_Q : y * c ∈ Qz zz :=
    ((H.hF3 (y * c) z hxcyc (IsConj.refl z)).shape_2AB zz
      ⟨hzzZ, (gamma_isConj_iff hxcyc ((y * c) * zz)).mpr hxcyc_zz⟩).2
  have hc_Q : c ∈ Qz zz := by
    have hmul : y * (y * c) = c := by rw [← mul_assoc, H.mul_self_a hyA, one_mul]
    rw [← hmul]
    exact (Qz zz).mul_mem hy_Q hyc_Q
  exact ⟨c, hc_Q, hcy, htc.symm, hc2, hcy2⟩

theorem gamma_fourA_row6A (H : GammaHyps a z) {y t : G} (hy : y ∈ orb4A a z a)
    (ht : t ∈ orb2A a y) (htb : t ∈ orb6A a ((a * y) ^ 2 * y)) :
    ∃ c : G, c ∈ Qz ((a * y) ^ 2) ∧ c * y = y * c ∧ c * t = t * c ∧ orderOf c = 2 ∧
      orderOf (c * y) = 2 := by
  let zz : G := (a * y) ^ 2
  let b : G := zz * y
  obtain ⟨hbA, hb_mul_y, hy_mul_b, _, _, _, _⟩ :=
    gamma_fourA_setup (zz := zz) (b := b) H hy rfl rfl
  have hyA : IsConj a y := hy.1
  have hzzZ : IsConj z zz := hy.2
  have htA : IsConj a t := ht.1
  have hyt : y * t = t * y := H.comm_of_orb2A hyA ht
  have hb_comm_y : b * y = y * b := by rw [hb_mul_y, hy_mul_b]
  have htb_a : t ∈ orb6A a b := htb
  have htb_ord : orderOf (b * t) = 6 := htb.2.1
  let c : G := (b * t) ^ 3
  have hcA : IsConj a c := htb.2.2
  have hc2 : orderOf c = 2 := H.orderOf_a hcA
  obtain ⟨hbc, htc, -, -⟩ :=
    tableV_dihedral (H.sq_a hbA) (H.sq_a htA) (hbA.symm.trans htA) (m := 3)
      (by rw [htb_ord])
  have hyb_comm : Commute y b := hb_comm_y.symm
  have hbt_comm : Commute y (b * t) := hyb_comm.mul_right hyt
  have hy_comm_c : y * c = c * y := hbt_comm.pow_right 3
  have hcy : c * y = y * c := hy_comm_c.symm
  have hczz : c * zz = zz * c := by
    have hcb : Commute c b := hbc.symm
    have h3 : Commute c (b * y) := hcb.mul_right hcy
    rwa [hb_mul_y] at h3
  have hinv : t * b = (b * t)⁻¹ := by rw [mul_inv_rev, H.inv_a htA, H.inv_a hbA]
  have htb3 : (t * b) ^ 3 = c := by
    rw [hinv, inv_pow]
    exact H.inv_a hcA
  have hbt_mem : b ∈ orb6A t t := by
    refine ⟨htA.symm.trans hbA, ?_, ?_⟩
    · rw [hinv, orderOf_inv, htb_ord]
    · rw [htb3]
      exact htA.symm.trans hcA
  have hy_2Att : y ∈ orb2A t t := by
    refine ⟨htA.symm.trans hyA, ?_⟩
    rw [← hyt]
    exact (gamma_isConj_iff htA (y * t)).mpr ht.2
  have hy_2Btb : y ∈ orb2B t z b :=
    ⟨htA.symm.trans hyA, by rw [hb_mul_y]; exact hzzZ⟩
  obtain ⟨hcase, -, -⟩ :=
    (H.h6A t z htA (IsConj.refl z)).case_ii b hbt_mem y ⟨hy_2Att, hy_2Btb⟩
  rw [htb3] at hcase
  have hcyA : IsConj a (c * y) := by
    rw [hcy]
    exact htA.trans hcase.1.1
  have hcy2 : orderOf (c * y) = 2 := H.orderOf_a hcyA
  have hbcyc : b * (y * c) = c * zz := by
    rw [← mul_assoc, hb_mul_y, ← hczz]
  have hczzA : IsConj a (c * zz) := by
    rw [← hbcyc]
    exact htA.trans hcase.2.2
  have hc_Q : c ∈ Qz zz :=
    ((H.hF3 c z hcA (IsConj.refl z)).shape_2AB zz
      ⟨hzzZ, (gamma_isConj_iff hcA (c * zz)).mpr hczzA⟩).2
  exact ⟨c, hc_Q, hcy, htc.symm, hc2, hcy2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
