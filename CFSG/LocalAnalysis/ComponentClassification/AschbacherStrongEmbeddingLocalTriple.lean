module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInvolutionClass
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCentralBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCentralQuotient

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

theorem stronglyEmbedded_of_isolated {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y} {y : Y}
    (hy : orderOf y = 2) (hH : H ≠ ⊤) (huniq : ∀ g : Y, y ∈ rightConjugate H g ↔ g ∈ H)
    (hcentral : InvolutionPointCentralSylow y) (hhull : involutionPointHull y = ⊤)
    (hiso : ∀ t ∈ involutionPointClass y, Commute y t → t = y) : fusionStronglyEmbedded H := by
  obtain ⟨S, hyS, hyc⟩ := hcentral
  have hycomm := commute_of_mem_center hyS hyc
  have hyorder : orderOf (⟨y, hyS⟩ : (S : Subgroup Y)) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hy
  have hwc : ∀ g : Y, g⁻¹ * ((⟨y, hyS⟩ : (S : Subgroup Y)) : Y) * g ∈ (S : Subgroup Y) →
      g⁻¹ * ((⟨y, hyS⟩ : (S : Subgroup Y)) : Y) * g = (⟨y, hyS⟩ : (S : Subgroup Y)) := by
    intro g hg
    exact hiso _ (class_conj_mem (distinguished_mem_pointClass y) g) (hycomm _ hg)
  obtain ⟨-, hycenter⟩ :=
    CFSG.Milestones.glauberman_zStar_central_sylow_involution S ⟨y, hyS⟩ hyc hyorder hwc
  let q := QuotientGroup.mk' (CFSG.oddCore Y)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hodd : Odd (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card Y
  have hclass : ∀ t ∈ involutionPointClass y, q t = q y := by
    rintro t ⟨g, rfl⟩
    change q (g⁻¹ * y * g) = q y
    rw [map_mul, map_mul, map_inv]
    have hc := Subgroup.mem_center_iff.mp hycenter (q g)
    change q g * q y = q y * q g at hc
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have hall : ∀ g : Y, q g ∈ Subgroup.zpowers (q y) := by
    intro g
    have hg : g ∈ involutionPointHull y := hhull ▸ Subgroup.mem_top g
    have hle : involutionPointHull y ≤ (Subgroup.zpowers (q y)).comap q := by
      refine (Subgroup.closure_le _).mpr fun t ht => ?_
      change q t ∈ Subgroup.zpowers (q y)
      rw [hclass t ht]
      exact Subgroup.mem_zpowers _
    exact hle hg
  have hqy2 : orderOf (q y) = 2 := orderOf_map_of_odd q hodd hy
  have hinvol : ∀ i : Y, orderOf i = 2 → i ∈ involutionPointClass y := by
    intro i hi
    have hiI := isInvolution_of_orderOf hi
    have hqiI := CFSG.ProperTwoGeneratedCore.involution_image_of_odd_kernel q hodd hiI
    have hqi : q i = q y := by
      rcases (mem_zpowers_of_orderOf_two hqy2).mp (hall i) with h | h
      · exact absurd h hqiI.ne_one
      · exact h
    obtain ⟨n, -, hn⟩ := CFSG.ProperTwoGeneratedCore.involutions_kernel_conjugate q hodd
      (isInvolution_of_orderOf hy) hiI hqi.symm
    exact ⟨n, hn⟩
  refine ⟨hH, ?_, ?_⟩
  · have hyH := mem_of_unique huniq
    have horder : orderOf (⟨y, hyH⟩ : H) = 2 := by rw [Subgroup.orderOf_mk]; exact hy
    exact even_iff_two_dvd.mpr (horder ▸ orderOf_dvd_natCard _)
  · intro g hg
    by_contra hnot
    obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom)) 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnot))
    have hiY : orderOf (i : Y) = 2 := (Subgroup.orderOf_coe i).trans hi
    have hicls := hinvol _ hiY
    obtain ⟨ω, hω⟩ := class_fixes_unique huniq hicls
    have hbase : (i : Y) • (QuotientGroup.mk 1 : Y ⧸ H) = QuotientGroup.mk 1 :=
      class_mem_iff_fixes_base.mp i.property.1
    have hgfix : (i : Y) • (QuotientGroup.mk g⁻¹ : Y ⧸ H) = QuotientGroup.mk g⁻¹ := by
      rw [smul_mk_eq_mk_iff, inv_inv]
      obtain ⟨h, hh, hhi⟩ := i.property.2
      rw [← hhi]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc,
        mul_inv_cancel_left, mul_inv_cancel, mul_one]
      exact hh
    have h1 := (hω _).mp hbase
    have h2 := (hω _).mp hgfix
    apply hg
    have h3 : (QuotientGroup.mk g⁻¹ : Y ⧸ H) = QuotientGroup.mk 1 := h2.trans h1.symm
    rw [mk_eq_base_iff] at h3
    exact H.inv_mem_iff.mp h3

theorem exists_triple_of_split {Y : Type*} [Group Y] [Finite Y] {M : Subgroup Y} {y v : Y}
    (hy : orderOf y = 2) (hycenter : y ∉ Subgroup.center Y)
    {t : Y} (ht : t ∈ involutionPointClass y) (hyt : Commute y t) (hne : t ≠ y)
    (hv : v ∈ Subgroup.center Y) (hv2 : v ^ 2 = 1)
    (hse : fusionStronglyEmbedded (M.subgroupOf (commutator Y)))
    (hcls : ∀ s ∈ involutionPointClass y, v⁻¹ * s ∈ commutator Y) :
    ∃ b ∈ involutionPointClass y, Commute y b ∧ Commute t b ∧ b ≠ t ∧ y * t * b = v := by
  let K := commutator Y
  have hvc : ∀ g : Y, g * v = v * g := fun g => Subgroup.mem_center_iff.mp hv g
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hv2)
  have hyy : y * y = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hy).1
  have htt := class_mul_self hy ht
  have hvi : ∀ g : Y, Commute v⁻¹ g := fun g =>
    (show Commute g v from hvc g).symm.inv_left
  have hsq : ∀ s ∈ involutionPointClass y, (v⁻¹ * s) ^ 2 = 1 := by
    intro s hs
    have hss := class_mul_self hy hs
    rw [hvinv, pow_two]
    calc v * s * (v * s) = v * (s * v) * s := by group
      _ = v * (v * s) * s := by rw [hvc s]
      _ = (v * v) * (s * s) := by group
      _ = 1 := by rw [← pow_two, hv2, hss, one_mul]
  have hne1 : ∀ s ∈ involutionPointClass y, v⁻¹ * s ≠ 1 := by
    intro s hs h
    have hsv : s = v := by
      calc s = v * (v⁻¹ * s) := by group
        _ = v := by rw [h, mul_one]
    exact hycenter (mem_center_of_class_mem_center hs (by rw [hsv]; exact hv))
  let kx : K := ⟨v⁻¹ * y, hcls y (distinguished_mem_pointClass y)⟩
  let kt : K := ⟨v⁻¹ * t, hcls t ht⟩
  have hkx : orderOf kx = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hsq y (distinguished_mem_pointClass y))
      (hne1 y (distinguished_mem_pointClass y))
  have hkt : orderOf kt = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hsq t ht) (hne1 t ht)
  have hcommY : Commute (v⁻¹ * y) (v⁻¹ * t) :=
    Commute.mul_left (hvi _) (Commute.mul_right (hvi y).symm hyt)
  have hcommK : Commute kx kt := Subtype.ext hcommY.eq
  have hkne : kt ≠ kx := by
    intro h
    apply hne
    have h' := congrArg (fun w : K => v * (w : Y)) h
    simpa only [kx, kt, mul_inv_cancel_left] using h'
  have hkk : kx * kx = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hkx).1
  have hktt : kt * kt = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hkt).1
  have hprod := orderOf_mul_of_commute hkk hktt hcommK hkne
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_stronglyEmbedded hse hkx hprod)
  have hcY : (c : Y) * (v⁻¹ * y) * (c : Y)⁻¹ = (v⁻¹ * y) * (v⁻¹ * t) :=
    congrArg Subtype.val hc
  have hb : (c : Y) * y * (c : Y)⁻¹ = v⁻¹ * (y * t) := by
    have h1 : (c : Y) * y * (c : Y)⁻¹ = v * ((c : Y) * (v⁻¹ * y) * (c : Y)⁻¹) := by
      calc (c : Y) * y * (c : Y)⁻¹ = (c : Y) * (v * (v⁻¹ * y)) * (c : Y)⁻¹ := by group
        _ = v * ((c : Y) * (v⁻¹ * y) * (c : Y)⁻¹) := by
            rw [← mul_assoc (c : Y) v, hvc (c : Y)]
            group
    rw [h1, hcY]
    calc v * ((v⁻¹ * y) * (v⁻¹ * t)) = y * (v⁻¹ * t) := by group
      _ = v⁻¹ * (y * t) := by rw [← mul_assoc, ← (hvi y).eq, mul_assoc]
  refine ⟨v⁻¹ * (y * t), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hb]
    simpa only [inv_inv] using class_conj_mem (distinguished_mem_pointClass y) (c : Y)⁻¹
  · exact (hvi y).symm.mul_right ((Commute.refl y).mul_right hyt)
  · exact (hvi t).symm.mul_right (hyt.symm.mul_right (Commute.refl t))
  · intro h
    apply hycenter
    have hyv : y = v := by
      have h' := congrArg (fun w => v * w * t⁻¹) h
      simp only [mul_inv_cancel_left, mul_assoc, mul_inv_cancel, mul_one] at h'
      calc y = v * t * t⁻¹ := by rw [← h']; group
        _ = v := by group
    rw [hyv]
    exact hv
  · have hytyt : y * t * (y * t) = 1 := by
      rw [mul_assoc, ← mul_assoc t y t, ← hyt.eq, mul_assoc, htt, mul_one, hyy]
    calc y * t * (v⁻¹ * (y * t)) = v⁻¹ * (y * t * (y * t)) := by
          rw [← mul_assoc, ← (hvi (y * t)).eq, mul_assoc]
      _ = v := by rw [hytyt, mul_one, hvinv]

end CFSG.ComponentClassification.AschbacherStrongEmbedding
