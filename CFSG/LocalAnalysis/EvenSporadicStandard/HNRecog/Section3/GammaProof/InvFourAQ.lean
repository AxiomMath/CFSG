module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzNo.Qz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_fourA_Q (H : GammaHyps a z) {y t c : G} (hy : y ∈ orb4A a z a)
    (ht : t ∈ orb2A a y) (hc : c ∈ Qz ((a * y) ^ 2)) (hcy : c * y = y * c)
    (hct : c * t = t * c) (hc2 : orderOf c = 2) (hcy2 : orderOf (c * y) = 2) :
    ∃ s : G, orderOf s = 2 ∧ s ∈ Gxyz a y t := by
  let zz : G := (a * y) ^ 2
  have hyA : IsConj a y := hy.1
  have hzz : IsConj z zz := hy.2
  have ha2 : a ^ 2 = 1 := H.sq_a (IsConj.refl a)
  have hy2 : y ^ 2 = 1 := H.sq_a hyA
  have haa : a * a = 1 := H.mul_self_a (IsConj.refl a)
  have hyy : y * y = 1 := H.mul_self_a hyA
  have hai : a⁻¹ = a := H.inv_a (IsConj.refl a)
  have hzz2 : zz * zz = 1 := by
    have h := H.sq_z hzz
    simpa [pow_two] using h
  have hord : orderOf (a * y) = 4 := tableV_orderOf_orb4A H.h hy
  obtain ⟨-, -, hazz_conj, -⟩ :=
    tableV_dihedral ha2 hy2 hyA (m := 2) (by rw [hord])
  have haQ : a ∈ Qz zz :=
    ((H.hF3.self).shape_2AB zz ⟨hzz, hazz_conj⟩).2
  have hF5 : IsF5Type a zz := isF5Type_of_isConj H.h (IsConj.refl a) hzz
  have hcomm_mem : ⁅a, c⁆ ∈ Subgroup.zpowers zz :=
    commutatorElement_mem_zpowers_of_mem_Qz hF5 haQ hc
  rw [gzNo_mem_zpowers_iff (H.orderOf_z hzz)] at hcomm_mem
  have hyt : y * t = t * y := H.comm_of_orb2A hyA ht
  have hcz : zz * c = c * zz := mem_Gx.mp (gzNo_Qz_le zz hc)
  rcases hcomm_mem with hcomm1 | hcommz
  · have hac : a * c = c * a := commutatorElement_eq_one_iff_mul_comm.mp hcomm1
    refine ⟨c, hc2, ?_⟩
    rw [mem_Gxyz, mem_Gx, mem_Gx, mem_Gx]
    exact ⟨hac, hcy.symm, hct.symm⟩
  · have hac_conj : a * c * a⁻¹ = zz * c := by
      have h := hcommz
      rw [commutatorElement_def] at h
      calc a * c * a⁻¹ = a * c * a⁻¹ * c⁻¹ * c := by
            rw [mul_assoc (a * c * a⁻¹) c⁻¹ c, inv_mul_cancel, mul_one]
        _ = zz * c := by rw [← h]
    have hay_conj : a * y * a⁻¹ = zz * y := by
      have hsq : (a * y) * (a * y) = zz := by
        change (a * y) * (a * y) = (a * y) ^ 2
        rw [pow_two]
      rw [hai]
      have h3 : a * y * a * (y * y) = zz * y := by
        calc a * y * a * (y * y) = ((a * y) * (a * y)) * y := by group
          _ = zz * y := by rw [hsq]
      rw [hyy, mul_one] at h3
      exact h3
    have hcy_a : a * (c * y) = (c * y) * a := by
      have h4 : a * (c * y) * a⁻¹ = c * y := by
        calc a * (c * y) * a⁻¹ = (a * c * a⁻¹) * (a * y * a⁻¹) := by group
          _ = (zz * c) * (zz * y) := by rw [hac_conj, hay_conj]
          _ = c * y := by
                rw [hcz, mul_assoc, ← mul_assoc zz zz y, hzz2, one_mul]
      calc a * (c * y) = a * (c * y) * (a * a) := by rw [haa, mul_one]
        _ = (a * (c * y) * a⁻¹) * a := by rw [hai]; group
        _ = (c * y) * a := by rw [h4]
    have hcy_y : y * (c * y) = (c * y) * y := by
      calc y * (c * y) = (y * c) * y := by group
        _ = (c * y) * y := by rw [← hcy]
    have hcy_t : t * (c * y) = (c * y) * t := by
      calc t * (c * y) = (t * c) * y := by group
        _ = (c * t) * y := by rw [← hct]
        _ = c * (t * y) := by group
        _ = c * (y * t) := by rw [← hyt]
        _ = (c * y) * t := by group
    refine ⟨c * y, hcy2, ?_⟩
    rw [mem_Gxyz, mem_Gx, mem_Gx, mem_Gx]
    exact ⟨hcy_a, hcy_y, hcy_t⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
