module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.GzBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Tau
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

private lemma mul_self_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rw [hx] at h
  simpa [pow_two] using h

private lemma mul_self_mul_self_of_comm {x y : G} (hcomm : y * x = x * y) (hx : x * x = 1)
    (hy : y * y = 1) : (x * y) * (x * y) = 1 := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hinv : (x * y)⁻¹ = x * y := by rw [mul_inv_rev, hyi, hxi, hcomm]
  calc (x * y) * (x * y) = (x * y) * (x * y)⁻¹ := by rw [hinv]
    _ = 1 := mul_inv_cancel _

private lemma iff_false_iff_not_iff {A P : Prop} (hA : ¬ A) : (A ↔ ¬ P) ↔ P := by
  constructor
  · intro hiff
    by_contra hP
    exact hA (hiff.mpr hP)
  · intro hP
    exact ⟨fun hA' _ => (hA hA').elim, fun hP' => (hP' hP).elim⟩

theorem involution_in_coset (h : F5Std a z) {w x y : G} (hw : IsConj z w) (hx : IsConj a x)
    (hwx : IsConj z (w * x)) (hy : ∃ q ∈ Qz w, y = x * q) (hy2 : orderOf y = 2) :
    ConjIn (Gx w) x y ∨ ConjIn (Gx w) (x * w) y := by
  classical
  obtain ⟨q, hq, hyq⟩ := hy
  have hF : F5Std a w := h.of_isConj (IsConj.refl a) hw
  have hcomm : w * x = x * w := h.mul_comm (Or.inr hw) (Or.inl hx) (Or.inr hwx)
  have hxGxw : x ∈ Gx w := mem_Gx.mpr hcomm
  have hwGxx : w ∈ Gx x := mem_Gx.mpr hcomm.symm
  have hxord : orderOf x = 2 := h.orderOf_eq_two (Or.inl hx)
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hxord
  have hww : w * w = 1 := mul_self_eq_one_of_orderOf_eq_two hF.typ.orderOf_z
  have hw2 : w ^ 2 = 1 := by rw [pow_two]; exact hww
  have hQz_le : Qz w ≤ Gx w := Subgroup.map_subtype_le _
  have hx_not_Qz : x ∉ Qz w := by
    intro hxQ
    have hxw : x ≠ w := by
      intro hxw
      exact not_isConj_of_isF5Type h.iface h.typ ((hxw ▸ hx).trans hw.symm)
    have hconj : IsConj x (w * x) := by
      have h1 : IsConj x (x * w) :=
        isConj_mul_of_mem_Qz hF.typ.cent_z hF.typ.orderOf_z hxord hxw hxQ
      simpa [← hcomm] using h1
    exact not_isConj_of_isF5Type h.iface h.typ (hx.trans (hconj.trans hwx.symm))
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy2] at h
    simpa [pow_two] using h
  have hxq_eq : x * q * x = q⁻¹ := by
    have h1 : (x * q) * (x * q) = 1 := by
      rw [← hyq]
      exact hyy
    exact mul_eq_one_iff_eq_inv.mp (by
      calc x * q * x * q = (x * q) * (x * q) := by rw [mul_assoc]
        _ = 1 := h1)
  have hqq : q * q = 1 := by
    rcases sq_mem_Qz hF hq with h1 | hw'
    · rwa [pow_two] at h1
    · exfalso
      have hqinv2 : q⁻¹ * q⁻¹ = w := by
        have h2 : q⁻¹ * q⁻¹ = (q * q)⁻¹ := (mul_inv_rev q q).symm
        rw [h2, ← pow_two, hw', inv_eq_of_mul_eq_one_right hww]
      have hqx : q * x = x * q⁻¹ := by
        calc q * x = ((x * x) * q) * x := by rw [hxx, one_mul]
          _ = x * (x * q * x) := by group
          _ = x * q⁻¹ := by rw [hxq_eq]
      have hconj : IsConj x (w * x) := by
        refine isConj_iff.mpr ⟨q, ?_⟩
        rw [hqx, mul_assoc, hqinv2, ← hcomm]
      exact not_isConj_of_isF5Type h.iface h.typ (hx.trans (hconj.trans hwx.symm))
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hqq
  have hxq : x * q = q * x := by
    have h := congrArg (fun t => t * x) hxq_eq
    rw [mul_assoc (x * q) x x, hxx, mul_one, hqi] at h
    exact h
  have hy_mem_Gxw : y ∈ Gx w := by
    rw [hyq]
    exact (Gx w).mul_mem hxGxw (hQz_le hq)
  have hy_not_Qz : y ∉ Qz w := by
    intro hyQ
    apply hx_not_Qz
    have hxeq : x = y * q⁻¹ := by rw [hyq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hxeq]
    exact (Qz w).mul_mem hyQ ((Qz w).inv_mem hq)
  have hyw_mem_Gxw : y * w ∈ Gx w := (Gx w).mul_mem hy_mem_Gxw (self_mem_Gx w)
  have hyw_not_Qz : y * w ∉ Qz w := by
    intro hywQ
    apply hy_not_Qz
    have hyeq : y = (y * w) * w := by rw [mul_assoc, hww, mul_one]
    rw [hyeq]
    exact (Qz w).mul_mem hywQ (self_mem_Qz hw2)
  have hyGxx : y ∈ Gx x := by
    rw [mem_Gx, hyq]
    calc x * (x * q) = (x * x) * q := by rw [mul_assoc]
      _ = q := by rw [hxx, one_mul]
      _ = (x * q) * x := by rw [mul_assoc, ← hxq, ← mul_assoc, hxx, one_mul]
  have hyw_mem_Gxx : y * w ∈ Gx x := (Gx x).mul_mem hyGxx hwGxx
  have hyw2 : (y * w) * (y * w) = 1 :=
    mul_self_mul_self_of_comm (mem_Gx.mp hy_mem_Gxw) hyy hww
  have orbit : ∀ c : G, c ∈ Gx w → c ∉ Qz w → IsConj a c → ConjIn (Gx w) x c :=
    fun c hcGx hcQ hcA =>
      hF.loc.gzOrbit.self.orbit_outA.1.transitive x ⟨hxGxw, hx_not_Qz, hx⟩ c
        ⟨hcGx, hcQ, hcA⟩
  by_cases hay : IsConj a y
  · by_cases hayw : IsConj a (y * w)
    · exfalso
      exact hy_not_Qz (mem_Qz_of_isConj_mul h.iface h.typ h.loc.fusion1 hay hw
        (mem_Gx.mp hy_mem_Gxw).symm hayw)
    · exact Or.inl (orbit y hy_mem_Gxw hy_not_Qz hay)
  · by_cases hayw : IsConj a (y * w)
    · right
      obtain ⟨k, hk, hkconj⟩ := orbit (y * w) hyw_mem_Gxw hyw_not_Qz hayw
      refine ⟨k, hk, ?_⟩
      have hkw : k * w * k⁻¹ = w := by
        rw [← mem_Gx.mp hk, mul_assoc, mul_inv_cancel, mul_one]
      calc k * (x * w) * k⁻¹ = (k * x * k⁻¹) * (k * w * k⁻¹) := by group
        _ = (y * w) * w := by rw [hkconj, hkw]
        _ = y := by rw [mul_assoc, hww, mul_one]
    · exfalso
      have hFx : F5Std x z := h.of_isConj hx (IsConj.refl z)
      have hmd := hFx.loc.fusion2.self.mem_derived_iff
      have hxConj_y : ¬ IsConj x y := fun hh => hay (hx.trans hh)
      have hxConj_yw : ¬ IsConj x (y * w) := fun hh => hayw (hx.trans hh)
      have hxConj_w : ¬ IsConj x w := fun hh =>
        not_isConj_of_isF5Type h.iface h.typ (hx.trans (hh.trans hw.symm))
      have hxConj_xw : ¬ IsConj x (x * w) := by
        intro hh
        have hz_xw : IsConj z (x * w) := by
          have h' := hwx
          rwa [hcomm] at h'
        exact not_isConj_of_isF5Type h.iface h.typ (hx.trans (hh.trans hz_xw.symm))
      have hq_ne_one : q ≠ 1 := by
        intro hq1
        apply hay
        rw [hyq, hq1, mul_one]
        exact hx
      have hqw : q ≠ w := by
        intro hqw
        apply hayw
        rw [hyq, hqw, mul_assoc, hww, mul_one]
        exact hx
      have hqOrder : orderOf q = 2 := orderOf_eq_prime (by rw [pow_two]; exact hqq) hq_ne_one
      have hqConj : IsConj q (q * w) :=
        isConj_mul_of_mem_Qz hF.typ.cent_z hF.typ.orderOf_z hqOrder hqw hq
      have hy2' : y ^ 2 = 1 := by rw [pow_two]; exact hyy
      have hyw2' : (y * w) ^ 2 = 1 := by rw [pow_two]; exact hyw2
      have hmd_w := hmd w hwGxx hw2
      have hmd_y := hmd y hyGxx hy2'
      have hmd_yw := hmd (y * w) hyw_mem_Gxx hyw2'
      have hw_not_der : w ∉ derivedOf (Gx x) := by
        rw [hmd_w]
        intro hiff
        exact hxConj_w (hiff.mpr hxConj_xw)
      have hxy : x * y = q := by rw [hyq, ← mul_assoc, hxx, one_mul]
      have hxyw : x * (y * w) = q * w := by rw [← mul_assoc, hxy]
      have hqw_iff : IsConj x (q * w) ↔ IsConj x q :=
        ⟨fun hh => hh.trans hqConj.symm, fun hh => hh.trans hqConj⟩
      have hy_der_iff : y ∈ derivedOf (Gx x) ↔ IsConj x q := by
        rw [hmd_y, hxy]
        exact iff_false_iff_not_iff hxConj_y
      have hyw_der_iff : y * w ∈ derivedOf (Gx x) ↔ IsConj x q := by
        rw [hmd_yw, hxyw, hqw_iff]
        exact iff_false_iff_not_iff hxConj_yw
      rcases em (IsConj x q) with hqA | hqA
      · have hyD : y ∈ derivedOf (Gx x) := hy_der_iff.mpr hqA
        have hywD : y * w ∈ derivedOf (Gx x) := hyw_der_iff.mpr hqA
        have hwD : w ∈ derivedOf (Gx x) := by
          have hm : y * (y * w) ∈ derivedOf (Gx x) := (derivedOf (Gx x)).mul_mem hyD hywD
          rwa [← mul_assoc, hyy, one_mul] at hm
        exact hw_not_der hwD
      · have hyD : y ∉ derivedOf (Gx x) := fun hh => hqA (hy_der_iff.mp hh)
        have hywD : y * w ∉ derivedOf (Gx x) := fun hh => hqA (hyw_der_iff.mp hh)
        obtain ⟨-, hidx⟩ := derived_Gx_a hFx
        have hwD : w ∈ derivedOf (Gx x) := by
          have hm := hidx y hyGxx (y * w) hyw_mem_Gxx hyD hywD
          rwa [← mul_assoc, hyy, one_mul] at hm
        exact hw_not_der hwD

end CFSG.EvenSporadicStandard.HNRecog.Section4
