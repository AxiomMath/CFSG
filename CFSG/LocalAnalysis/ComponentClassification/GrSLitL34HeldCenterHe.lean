module

public import CFSG.RankThree.PartOne.KS.HeFiveCentralizers
public import CFSG.RankThree.PartOne.KS.PlaneWitnessClass
public import Certificates.Certificate22221

public section

namespace CFSG.ComponentClassification.GrSLit.L34HeldCenter

open Subgroup CFSG.RankThree.PartOne CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

theorem noFour_parts (i : ℕ) (hi : i < heFiveC0Cert.pts.size) :
    (!(eqA 8330 (compA 8330 (compA 8330 heFiveC0Cert.pts[i]! heFiveC0Cert.pts[i]!)
        (compA 8330 heFiveC0Cert.pts[i]! heFiveC0Cert.pts[i]!)) (idA 8330)) ||
      eqA 8330 (compA 8330 heFiveC0Cert.pts[i]! heFiveC0Cert.pts[i]!) (idA 8330) ||
      !(siftA 8330 heLevels heBase.toArray 0 heFiveC0Cert.pts[i]!)) = true := by
  have h := Certificates.certificate22221
  rw [heFiveNoFourOK] at h
  exact allLt_spec h hi

theorem not_mem_heP_of_orderOf_eq_four
    {g : Equiv.Perm (Fin 8330)}
    (hg : g ∈ heFiveC0) (h4 : orderOf g = 4) : g ∉ heP := by
  intro hP
  obtain ⟨-, hcent, -, -⟩ := heFive_case0_check
  obtain ⟨i, hi, hrep⟩ := enumOK_exists_rep heFiveKeys_lt (centOKP_enum hcent) hg
  have hc := noFour_parts i hi
  have r2 : Rep 8330 (compA 8330 heFiveC0Cert.pts[i]! heFiveC0Cert.pts[i]!) (g * g) :=
    rep_compA hrep hrep
  have hg4 : g * g * (g * g) = 1 := by
    have h := pow_orderOf_eq_one g
    rw [h4] at h
    rw [← h]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hg2 : g * g ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one (show g ^ 2 = 1 by rw [sq, h])
    rw [h4] at h'
    exact absurd h' (by decide)
  have e4 := (eqA_iff (rep_compA r2 r2) rep_idA).2 hg4
  have e2 : eqA 8330 (compA 8330 heFiveC0Cert.pts[i]! heFiveC0Cert.pts[i]!) (idA 8330) = false :=
    Bool.eq_false_iff.2 fun h => hg2 ((eqA_iff r2 rep_idA).1 h)
  have hs : siftA 8330 heLevels heBase.toArray 0 heFiveC0Cert.pts[i]! = true :=
    (mem_heP_iff_siftA hrep).2 hP
  rw [e4, e2, hs] at hc
  exact absurd hc (by decide)

theorem heP_no_twenty
    {x y : Equiv.Perm (Fin 8330)}
    (hx : x ∈ heP) (hy : y ∈ heP) (hxy : x * y = y * x) (h4 : orderOf x = 4)
    (h5 : orderOf y = 5) : False := by
  obtain ⟨g, hgP, hgQ⟩ := exists_conj_mem_sylow (by norm_num) heFiveQ_sylow hy h5
  have hz : g⁻¹ * y * g = MulAut.conj g⁻¹ y := by simp
  have hz5 : orderOf (g⁻¹ * y * g) = 5 := by rw [hz, MulEquiv.orderOf_eq, h5]
  have hmem : zpowers (g⁻¹ * y * g) ∈
      {H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heFiveQ ∧ Nat.card H = 5} :=
    ⟨zpowers_le.2 hgQ, by rw [Nat.card_zpowers, hz5]⟩
  rw [R3E_He_full_five_centralizer_structures.2.1.1] at hmem
  obtain ⟨j, hj⟩ := hmem
  have hxj : heFiveLine j ∈ zpowers (g⁻¹ * y * g) := hj ▸ mem_zpowers _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hxj
  obtain ⟨hhR, hh⟩ := heFiveTransporter_spec j
  rw [heFiveRecordOf_eq j] at hh
  set h := heFiveTransporter j with hhdef
  set c := h⁻¹ * g⁻¹ with hc
  have hcR : c ∈ heAutGroup :=
    mul_mem (inv_mem hhR) (inv_mem (heP_le_heAutGroup hgP))
  have hx0 : heFiveLine 0 = (c * y * c⁻¹) ^ k := by
    have e1 : c * y * c⁻¹ = MulAut.conj h⁻¹ (g⁻¹ * y * g) := by
      simp only [hc, MulAut.conj_apply, mul_inv_rev, inv_inv]
      group
    rw [e1, ← map_zpow, hk, ← hh, MulAut.conj_apply]
    group
  set x' := c * x * c⁻¹ with hx'
  have hcomm : x' * (c * y * c⁻¹) = (c * y * c⁻¹) * x' := by
    simp only [hx']
    calc c * x * c⁻¹ * (c * y * c⁻¹) = c * (x * y) * c⁻¹ := by group
      _ = c * (y * x) * c⁻¹ := by rw [hxy]
      _ = c * y * c⁻¹ * (c * x * c⁻¹) := by group
  have hx'C : x' ∈ heFiveC0 := by
    rw [heFiveC0_spec.1]
    refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · rw [hx0]
      exact ((Commute.zpow_left (show Commute (c * y * c⁻¹) x' from hcomm.symm) k).eq).symm
    · exact mul_mem (mul_mem hcR (heP_le_heAutGroup hx)) (inv_mem hcR)
  have hx'P : x' ∈ heP := (mem_normalizer_iff.1 (heAutGroup_le_normalizer hcR) x).1 hx
  have hx'4 : orderOf x' = 4 := by
    rw [show x' = MulAut.conj c x by simp [hx', MulAut.conj_apply], MulEquiv.orderOf_eq, h4]
  exact not_mem_heP_of_orderOf_eq_four hx'C hx'4 hx'P

end CFSG.ComponentClassification.GrSLit.L34HeldCenter
