module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec11d2_twoCoreIn_le (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem sec11d2_mem_twoCoreIn_iff {X : Subgroup G} {x : G} (hx : x ∈ X) :
    x ∈ twoCoreIn X ↔ (⟨x, hx⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by
  unfold twoCoreIn CFSG.inSubgroup
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem sec11d2_twoCoreIn_map (φ : G ≃* G) (H H' : Subgroup G)
    (h : H.map φ.toMonoidHom = H') :
    twoCoreIn H' = (twoCoreIn H).map φ.toMonoidHom := by
  have key := CFSG.pCore_map_iso 2 ((MulEquiv.subgroupMap φ H).trans (MulEquiv.subgroupCongr h))
  unfold twoCoreIn CFSG.inSubgroup
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem sec11d2_twoCoreIn_conj {K K' : Subgroup G} {a : G}
    (hK : CFSG.conjugate K a = K') {x : G} (hx : x ∈ twoCoreIn K) :
    a⁻¹ * x * a ∈ twoCoreIn K' := by
  have h : K.map (MulAut.conj a⁻¹).toMonoidHom = K' := hK
  rw [sec11d2_twoCoreIn_map (MulAut.conj a⁻¹) K K' h]
  refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
  simp [MulAut.conj_apply]

private theorem sec11d2_conjugate_swap {K K' : Subgroup G} {a : G} (haa : a * a = 1)
    (h : CFSG.conjugate K a = K') : CFSG.conjugate K' a = K := by
  rw [← h]
  unfold CFSG.conjugate
  rw [Subgroup.map_map]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hid : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hainv,
      inv_inv, MonoidHom.id_apply]
    calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [haa]; group
  rw [hid, Subgroup.map_id]

private theorem sec11d2_eq_neg_one {X : Subgroup G} (e : ↥X ≃* SL23) {z : G}
    (hz : z ∈ X) (hz2 : orderOf z = 2) : e ⟨z, hz⟩ = -1 := by
  have hsq : (⟨z, hz⟩ : ↥X) * ⟨z, hz⟩ = 1 := by
    apply Subtype.ext
    change z * z = (1 : G)
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have hsq' : e ⟨z, hz⟩ * e ⟨z, hz⟩ = 1 := by rw [← map_mul, hsq, map_one]
  rcases sl23_unique_involution _ hsq' with h | h
  · exfalso
    have hz1 : (⟨z, hz⟩ : ↥X) = 1 := by apply e.injective; rw [h, map_one]
    have hzG : z = 1 := by simpa using congrArg Subtype.val hz1
    have : orderOf z = 1 := by rw [hzG]; exact orderOf_one
    omega
  · exact h

private theorem sec11d2_mem_zpowers_of_sq {X : Subgroup G} (e : ↥X ≃* SL23) {z w : G}
    (hz : z ∈ X) (hz2 : orderOf z = 2) (hw : w ∈ X) (hw2 : w * w = 1) : w ∈ zpowers z := by
  have hw' : (⟨w, hw⟩ : ↥X) * ⟨w, hw⟩ = 1 := Subtype.ext (by simpa using hw2)
  have hwe : e ⟨w, hw⟩ * e ⟨w, hw⟩ = 1 := by rw [← map_mul, hw', map_one]
  rcases sl23_unique_involution (e ⟨w, hw⟩) hwe with h | h
  · have hw1 : (⟨w, hw⟩ : ↥X) = 1 := by apply e.injective; rw [h, map_one]
    rw [show w = 1 from congrArg Subtype.val hw1]
    exact Subgroup.one_mem _
  · have hwz : (⟨w, hw⟩ : ↥X) = ⟨z, hz⟩ := by
      apply e.injective
      rw [h, sec11d2_eq_neg_one e hz hz2]
    rw [show w = z from congrArg Subtype.val hwz]
    exact Subgroup.mem_zpowers z

private theorem sec11d2_z_mem_twoCoreIn {X : Subgroup G} (e : ↥X ≃* SL23) {z : G} (hz : z ∈ X)
    (hz2 : orderOf z = 2) : z ∈ twoCoreIn X := by
  rw [sec11d2_mem_twoCoreIn_iff hz]
  have hmem : e ⟨z, hz⟩ ∈ CFSG.pCore 2 SL23 := by
    rw [sec11d2_eq_neg_one e hz hz2]
    exact sl23_neg_one_mem_pCore
  rw [← CFSG.pCore_map_iso 2 e] at hmem
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
  have hy' : y = ⟨z, hz⟩ := e.injective hye
  rwa [hy'] at hy

theorem sec11d2_zpowers_cases {z c : G} (hz : z * z = 1) (hc : c ∈ zpowers z) :
    c = 1 ∨ c = z := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [← hn, hk, zpow_mul, h2, one_zpow]
  · right
    rw [← hn, hk, zpow_add, zpow_one, zpow_mul, h2, one_zpow, one_mul]

private theorem sec11d2_zpowers_sq {z c : G} (hz : z * z = 1) (hc : c ∈ zpowers z) :
    c * c = 1 := by
  rcases sec11d2_zpowers_cases hz hc with h | h
  · rw [h, one_mul]
  · rw [h, hz]

theorem sec11d2_mem_Qi [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {q : G} (hq : q ∈ secQ K1 K2) (hq2 : q * q = z) :
    q ∈ twoCoreIn K1 ∨ q ∈ twoCoreIn K2 := by
  obtain ⟨e1⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  obtain ⟨e2⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).2
  have hsup := sec10KS_twoCore_sup hP5 hC5 hpsp hctx
  have hcommQ : ∀ a ∈ twoCoreIn K1, ∀ b ∈ twoCoreIn K2, a * b = b * a := fun a ha b hb =>
    sec10Z_comm hP5 hpsp hctx a (sec11d2_twoCoreIn_le K1 ha) b (sec11d2_twoCoreIn_le K2 hb)
  obtain ⟨q1, hq1, q2, hq2m, hqeq⟩ :=
    exists_mul_of_mem_sup_of_commute hcommQ (by rw [← hsup]; exact hq)
  have hq1K1 : q1 ∈ K1 := sec11d2_twoCoreIn_le K1 hq1
  have hq2K2 : q2 ∈ K2 := sec11d2_twoCoreIn_le K2 hq2m
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  obtain ⟨-, hzsq, -, -, hz1⟩ := sec11_invols hctx
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  have hzK2 : z ∈ K2 := hctx.pocket2.1
  have hzQ1 : z ∈ twoCoreIn K1 := sec11d2_z_mem_twoCoreIn e1 hzK1 hz2
  have hzQ2 : z ∈ twoCoreIn K2 := sec11d2_z_mem_twoCoreIn e2 hzK2 hz2
  have hsq : q * q = (q1 * q1) * (q2 * q2) := by
    rw [hqeq]
    calc (q1 * q2) * (q1 * q2) = q1 * (q2 * q1) * q2 := by group
      _ = q1 * (q1 * q2) * q2 := by rw [← hcommQ q1 hq1 q2 hq2m]
      _ = (q1 * q1) * (q2 * q2) := by group
  have h1 : q1 * q1 ∈ zpowers z := (sec10KS_Qi_elem hP5 hC5 hpsp hctx q1 hq1 q1 hq1).2
  have h2 : q2 * q2 ∈ zpowers z :=
    (sec10KS_Qi_elem hP5 hC5 hpsp hctx.swap q2 hq2m q2 hq2m).2
  rcases sec11d2_zpowers_cases hzsq h1 with e1' | e1' <;>
    rcases sec11d2_zpowers_cases hzsq h2 with e2' | e2'
  · exfalso
    rw [e1', e2', one_mul] at hsq
    exact hz1 (hq2.symm.trans hsq)
  · right
    have hq1z : q1 ∈ zpowers z := sec11d2_mem_zpowers_of_sq e1 hzK1 hz2 hq1K1 e1'
    rw [hqeq]
    exact Subgroup.mul_mem _ (zpowers_le.mpr hzQ2 hq1z) hq2m
  · left
    have hq2z : q2 ∈ zpowers z := sec11d2_mem_zpowers_of_sq e2 hzK2 hz2 hq2K2 e2'
    rw [hqeq]
    exact Subgroup.mul_mem _ hq1 (zpowers_le.mpr hzQ1 hq2z)
  · exfalso
    rw [e1', e2', hzsq] at hsq
    exact hz1 (hq2.symm.trans hsq)

theorem sec11d2_swap_Q1 [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {a q : G} (hswap : CFSG.conjugate K1 a = K2)
    (hq : q ∈ twoCoreIn K1) (hq2 : q * q = z) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ b ∈ twoCoreIn K1, b * z = z * b) :
    (a⁻¹ * q * a) * q = q * (a⁻¹ * q * a) ∧ a⁻¹ * q * a ≠ q ∧ a⁻¹ * q * a ≠ q * z := by
  have hcomm : ∀ x ∈ twoCoreIn K1, ∀ y ∈ twoCoreIn K2, x * y = y * x := fun x hx y hy =>
    sec10Z_comm hP5 hpsp hctx x (sec11d2_twoCoreIn_le K1 hx) y (sec11d2_twoCoreIn_le K2 hy)
  have hqa : a⁻¹ * q * a ∈ twoCoreIn K2 := sec11d2_twoCoreIn_conj hswap hq
  have hcentral : ∀ y ∈ twoCoreIn K2, y = q ∨ y = q * z → False := by
    intro y hy hyq
    have hcq : ∀ b ∈ twoCoreIn K1, q * b = b * q := by
      intro b hb
      rcases hyq with hyq | hyq
      · rw [hyq] at hy
        exact (hcomm b hb q hy).symm
      · rw [hyq] at hy
        have h1 := hcomm b hb (q * z) hy
        have h2 : (b * q) * z = (q * b) * z := by
          calc (b * q) * z = b * (q * z) := by group
            _ = (q * z) * b := h1
            _ = q * (z * b) := by group
            _ = q * (b * z) := by rw [hzc b hb]
            _ = (q * b) * z := by group
        exact (mul_right_cancel h2).symm
    have hqz : q ∈ zpowers z := sec10KS_Qi_center hP5 hC5 hpsp hctx q hq hcq
    exact hz1 (hq2.symm.trans (sec11d2_zpowers_sq hz2 hqz))
  refine ⟨(hcomm q hq _ hqa).symm, fun h => hcentral _ hqa (Or.inl h),
    fun h => hcentral _ hqa (Or.inr h)⟩

theorem sec11d2_swap_Q [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {a q : G} (hswap : CFSG.conjugate K1 a = K2)
    (haa : a * a = 1) (hq : q ∈ secQ K1 K2) (hq2 : q * q = z)
    (hQz : ∀ y ∈ secQ K1 K2, y * z = z * y) :
    (a⁻¹ * q * a) * q = q * (a⁻¹ * q * a) ∧ a⁻¹ * q * a ≠ q ∧ a⁻¹ * q * a ≠ q * z := by
  obtain ⟨-, hz2, -, -, hz1⟩ := sec11_invols hctx
  have hsup := sec10KS_twoCore_sup hP5 hC5 hpsp hctx
  rcases sec11d2_mem_Qi hP5 hC5 hpsp hctx hq hq2 with h | h
  · exact sec11d2_swap_Q1 hP5 hC5 hpsp hctx hswap h hq2 hz2 hz1
      (fun b hb => hQz b (by rw [hsup]; exact Subgroup.mem_sup_left hb))
  · exact sec11d2_swap_Q1 hP5 hC5 hpsp hctx.swap (sec11d2_conjugate_swap haa hswap) h hq2 hz2
      hz1 (fun b hb => hQz b (by rw [hsup]; exact Subgroup.mem_sup_right hb))

end CFSG.OddStandard.SmallF3.Omega
