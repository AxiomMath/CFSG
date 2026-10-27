module

public import Certificates.Certificate4029
public import CFSG.Sporadic.J4.QT2LocBasic

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2

@[expose] def PentData (V : Subgroup ↥J) (y : ↥J) : Prop :=
  Nat.card V = 16 ∧ (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) ∧ (∀ a ∈ V, a * a = 1) ∧
    y ∈ Subgroup.normalizer (V : Set ↥J) ∧ orderOf y = 5 ∧ ∀ v ∈ V, y * v = v * y → v = 1

theorem pentData_map_cm (m : ↥J) {V : Subgroup ↥J} {y : ↥J} (h : PentData V y) :
    PentData (V.map (cm m)) (cm m y) := by
  obtain ⟨hc, hab, hsq, hx, hx5, hfpf⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (cm_injective m)]
    exact hc
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show m * a * m⁻¹ * (m * b * m⁻¹) = m * b * m⁻¹ * (m * a * m⁻¹)
    calc m * a * m⁻¹ * (m * b * m⁻¹) = m * (a * b) * m⁻¹ := by group
      _ = m * (b * a) * m⁻¹ := by rw [hab a ha b hb]
      _ = m * b * m⁻¹ * (m * a * m⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    show m * a * m⁻¹ * (m * a * m⁻¹) = 1
    calc m * a * m⁻¹ * (m * a * m⁻¹) = m * (a * a) * m⁻¹ := by group
      _ = 1 := by rw [hsq a ha]; group
  · have e := normalizer_map_equiv_eq (MulAut.conj m) V
    change cm m y ∈ Subgroup.normalizer ((V.map (MulAut.conj m).toMonoidHom : Subgroup ↥J) :
      Set ↥J)
    rw [e]
    exact ⟨y, hx, rfl⟩
  · have h5 := (MulAut.conj m).orderOf_eq y
    rw [MulAut.conj_apply] at h5
    rw [cm_apply, h5]
    exact hx5
  · rintro _ ⟨v, hv, rfl⟩ hcomm
    have h1 : y * v = v * y := by
      have : m * y * m⁻¹ * (m * v * m⁻¹) = m * v * m⁻¹ * (m * y * m⁻¹) := hcomm
      have h2 : m * (y * v) * m⁻¹ = m * (v * y) * m⁻¹ := by
        calc m * (y * v) * m⁻¹ = m * y * m⁻¹ * (m * v * m⁻¹) := by group
          _ = m * v * m⁻¹ * (m * y * m⁻¹) := this
          _ = m * (v * y) * m⁻¹ := by group
      simpa using h2
    have := hfpf v hv h1
    rw [this]
    simp [cm_apply]

theorem fpfV_common_fixed_xfv
    {V : Subgroup ↥J} (hV : FpfV V) (h : HasCommonFixedPt V) :
    ∃ k : ↥J, XfV (V.map (cm k)) := by
  have hM : MatFacts := Certificates.certificate4029.basic.mat
  obtain ⟨y, hyN, hy5, hfpf, g, hVg, hyg⟩ := h
  have hP : PentData V y := ⟨hV.1, hV.2.1, hV.2.2.1, hyN, hy5, hfpf⟩
  have hP1 := pentData_map_cm g⁻¹ hP
  have hVH : V.map (cm g⁻¹) ≤ Hj := by
    have := Subgroup.map_mono (f := cm g⁻¹) hVg
    rwa [map_cm_inv_map_cm] at this
  have hyH : cm g⁻¹ y ∈ Hj := by
    have : cm g⁻¹ y ∈ (Hj.map (cm g)).map (cm g⁻¹) := ⟨y, hyg, rfl⟩
    rwa [map_cm_inv_map_cm] at this
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨h1, k, hk⟩ := exists_conj_pow_of_card (G := ↥Hj) (p := 5)
    (card_Hj_factorization_five_b Certificates.certificate4029.basic) (x := ⟨fiveElt, fiveElt_mem_Hj⟩)
    (y := ⟨cm g⁻¹ y, hyH⟩) (by rw [Subgroup.orderOf_mk]; exact orderOf_fiveElt hM)
    (by rw [Subgroup.orderOf_mk]; exact hP1.2.2.2.2.1)
  have hk' : cm g⁻¹ y = (h1 : ↥J) * fiveElt ^ k * (h1 : ↥J)⁻¹ := by
    have := congrArg Subtype.val hk
    simpa using this
  have hk5 : fiveElt ^ k = fiveElt ^ (k % 5) := by
    conv_lhs => rw [← Nat.div_add_mod k 5, pow_add, pow_mul, fiveElt_pow hM, one_pow, one_mul]
  have hkne : k % 5 ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk5
    have hx1 : cm g⁻¹ y = 1 := by
      rw [hk', hk5]
      group
    have := hP1.2.2.2.2.1
    rw [hx1, orderOf_one] at this
    omega
  have hkr : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  have hP2 := pentData_map_cm (h1 : ↥J)⁻¹ hP1
  have e : cm (h1 : ↥J)⁻¹ (cm g⁻¹ y) = fiveElt ^ (k % 5) := by
    rw [cm_apply, hk', ← hk5]
    group
  rw [e] at hP2
  obtain ⟨hc2, hab2, hsq2, hN2, -, hfpf2⟩ := hP2
  refine ⟨(h1 : ↥J)⁻¹ * g⁻¹, ?_⟩
  rw [← map_cm_map_cm g⁻¹ (h1 : ↥J)⁻¹ V]
  refine ⟨?_, hc2, hab2, hsq2, ?_, xi_fpf hfpf2⟩
  · rintro _ ⟨a, ha, rfl⟩
    have := hVH ha
    have h3 : (h1 : ↥J)⁻¹ * a * (h1 : ↥J) ∈ Hj :=
      Hj.mul_mem (Hj.mul_mem (Hj.inv_mem h1.2) this) h1.2
    simpa [cm_apply] using h3
  · exact xi_conj_mem hM hkr (fun v hv => (Subgroup.mem_normalizer_iff.1 hN2 v).1 hv)

end CFSG.QuasithinUnique.A5
