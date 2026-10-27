module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.InvFourAQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.InvFourARows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.InvFourACount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_inv_fourA (H : GammaHyps a z) {y t : G} (hy : y ∈ orb4A a z a)
    (ht : t ∈ orb2A a y) : ∃ s : G, orderOf s = 2 ∧ s ∈ Gxyz a y t := by
  let zz : G := (a * y) ^ 2
  let b : G := zz * y
  have hyA : IsConj a y := hy.1
  have hzzZ : IsConj z zz := hy.2
  have htA : IsConj a t := ht.1
  have hyt : y * t = t * y := H.comm_of_orb2A hyA ht
  have hyy : y * y = 1 := H.mul_self_a hyA
  have ha2 : a ^ 2 = 1 := H.sq_a (IsConj.refl a)
  have hy2 : y ^ 2 = 1 := H.sq_a hyA
  have hord : orderOf (a * y) = 4 := tableV_orderOf_orb4A H.h hy
  obtain ⟨ha_zz, hy_zz, -, hyzz⟩ :=
    tableV_dihedral ha2 hy2 hyA (m := 2) (by rw [hord])
  have hbA : IsConj a b := by
    change IsConj a (zz * y)
    rw [hy_zz.symm]
    exact hyzz
  have hb_mul_y : b * y = zz := by
    show (zz * y) * y = zz
    rw [mul_assoc, hyy, mul_one]
  have hy_mul_b : y * b = zz := by
    show y * (zz * y) = zz
    rw [← mul_assoc, hy_zz, mul_assoc, hyy, mul_one]
  have hb_comm_y : b * y = y * b := by rw [hb_mul_y, hy_mul_b]
  by_cases hbt_comm : t * b = b * t
  · refine ⟨zz, H.orderOf_z hzzZ, ?_⟩
    rw [mem_Gxyz, mem_Gx, mem_Gx, mem_Gx]
    refine ⟨ha_zz, hy_zz, ?_⟩
    rw [← hb_mul_y]
    calc t * (b * y) = (t * b) * y := by group
      _ = (b * t) * y := by rw [hbt_comm]
      _ = b * (t * y) := by group
      _ = b * (y * t) := by rw [← hyt]
      _ = (b * y) * t := by group
  · have hbtA : IsConj b t := (gamma_isConj_iff hbA t).2 htA
    have hy_mem_Gxy : y ∈ Gxy b t := by
      rw [mem_Gxy]
      exact ⟨mem_Gx.2 hb_comm_y, mem_Gx.2 hyt.symm⟩
    have hnotconj : ¬ IsConj (b * y) (t * y) := by
      intro hconj
      have htyA : IsConj a (t * y) := by rw [← hyt]; exact ht.2
      have hzz_ty : IsConj zz (t * y) := by
        rw [hb_mul_y] at hconj
        exact hconj
      exact H.not_isConj_both htyA (hzzZ.trans hzz_ty)
    have hbt_even : Even (orderOf (b * t)) :=
      (H.hPar b z hbA (IsConj.refl z)).even_of_not_conj t y hbtA (H.orderOf_a hyA)
        hy_mem_Gxy hnotconj
    have hbase : t ∈ tab5Base b := ⟨hbtA, hbt_even⟩
    obtain ⟨i, hi⟩ := (H.hT5 b z hbA (IsConj.refl z)).partition.cover t hbase
    fin_cases i
    · exfalso
      have hi0 : t ∈ orb2A b b := hi
      have hi' : t ∈ orb2A a b := (gamma_orb2A_eq hbA b) ▸ hi0
      exact hbt_comm (H.comm_of_orb2A hbA hi').symm
    · exfalso
      have hi0 : t ∈ orb2B b z b := hi
      have hi' : t ∈ orb2B a z b := (gamma_orb2B_eq hbA z b) ▸ hi0
      exact hbt_comm (H.comm_of_orb2B hbA hi').symm
    · have hi0 : t ∈ orb4A b z b := hi
      obtain ⟨c, hc, hcy, hct, hc2, hcy2⟩ :=
        gamma_fourA_row4A H hy ht ((gamma_orb4A_eq hbA z b) ▸ hi0)
      exact gamma_fourA_Q H hy ht hc hcy hct hc2 hcy2
    · have hi0 : t ∈ orb4B b b := hi
      exact gamma_fourA_row4B H hy ht ((gamma_orb4B_eq hbA b) ▸ hi0)
    · have hi0 : t ∈ orb6A b b := hi
      obtain ⟨c, hc, hcy, hct, hc2, hcy2⟩ :=
        gamma_fourA_row6A H hy ht ((gamma_orb6A_eq hbA b) ▸ hi0)
      exact gamma_fourA_Q H hy ht hc hcy hct hc2 hcy2

end CFSG.EvenSporadicStandard.HNRecog.Section3
