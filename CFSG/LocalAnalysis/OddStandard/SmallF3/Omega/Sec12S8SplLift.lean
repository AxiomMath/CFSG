module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplCoord

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma s8_k4_lift_step1 {H : Type} [Group H] {V1 : Subgroup H}
    {φ : (Fin 5 → ZMod 2) → H} (hφ : Sec128Coord V1 φ) (p : Equiv.Perm (Fin 5))
    (hp : ∀ v : Fin 5 → ZMod 2, permVec p (permVec p v) = v)
    (hfree : ∀ s : Fin 5 → ZMod 2, IsEvenVec s → permVec p s = s →
      ∃ u : Fin 5 → ZMod 2, IsEvenVec u ∧ s = u + permVec p u)
    {x : H} (hx : ∀ v : Fin 5 → ZMod 2, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec p v))
    (hxx : x * x ∈ V1) :
    ∃ u : Fin 5 → ZMod 2, IsEvenVec u ∧ (x * φ u) * (x * φ u) = 1 := by
  obtain ⟨s, hs, hsv⟩ := hφ.surj (x * x) hxx
  have hperm_eq : φ (permVec p s) = φ s := by
    rw [← hx s hs, hsv]
    group
  have hfix : permVec p s = s :=
    hφ.eq_of_eq' (s8_isEvenVec_permVec p hs) hs hperm_eq
  obtain ⟨u, hu, hueq⟩ := hfree s hs hfix
  refine ⟨u, hu, ?_⟩
  have hw : φ (permVec p u) = x⁻¹ * φ u * x := by
    have h := hx (permVec p u) (s8_isEvenVec_permVec p hu)
    rw [hp u] at h
    calc φ (permVec p u) = x⁻¹ * (x * φ (permVec p u) * x⁻¹) * x := by group
      _ = x⁻¹ * φ u * x := by rw [h]
  have hzero : s + permVec p u + u = 0 := by
    rw [hueq, add_assoc u (permVec p u) (permVec p u), s8_add_self (permVec p u), add_zero,
      s8_add_self u]
  calc (x * φ u) * (x * φ u)
      = (x * x) * (x⁻¹ * φ u * x) * φ u := by group
    _ = φ s * φ (permVec p u) * φ u := by rw [← hsv, ← hw]
    _ = φ (s + permVec p u) * φ u := by
      rw [← hφ.mul s (permVec p u) hs (s8_isEvenVec_permVec p hu)]
    _ = φ (s + permVec p u + u) := by
      rw [← hφ.mul (s + permVec p u) u (s8_isEvenVec_add hs (s8_isEvenVec_permVec p hu)) hu]
    _ = φ 0 := by rw [hzero]
    _ = 1 := hφ.map_zero'

theorem s8_k4_lift {H : Type} [Group H] {V1 : Subgroup H} (hn : V1.Normal)
    {φ : (Fin 5 → ZMod 2) → H} (hφ : Sec128Coord V1 φ) {a b : H}
    (ha : ∀ v : Fin 5 → ZMod 2, IsEvenVec v → a * φ v * a⁻¹ = φ (permVec s8Pa v))
    (hb : ∀ v : Fin 5 → ZMod 2, IsEvenVec v → b * φ v * b⁻¹ = φ (permVec s8Pb v))
    (haa : a * a ∈ V1) (hbb : b * b ∈ V1) (hab : a * b * a⁻¹ * b⁻¹ ∈ V1) :
    ∃ a' b' : H, a'⁻¹ * a ∈ V1 ∧ b'⁻¹ * b ∈ V1 ∧ a' * a' = 1 ∧ b' * b' = 1 ∧
      a' * b' = b' * a' := by
  haveI : V1.Normal := hn
  obtain ⟨u, hu, hau⟩ :=
    s8_k4_lift_step1 hφ s8Pa s8_permVec_sq_a s8_fin_free_a ha haa
  obtain ⟨w, hw, hbw⟩ :=
    s8_k4_lift_step1 hφ s8Pb s8_permVec_sq_b s8_fin_free_b hb hbb
  set a1 : H := a * φ u with ha1
  set b1 : H := b * φ w with hb1
  have ha1sq : a1 * a1 = 1 := by rw [ha1]; exact hau
  have hb1sq : b1 * b1 = 1 := by rw [hb1]; exact hbw
  have ha1inv_eq : a1⁻¹ = a1 := inv_eq_of_mul_eq_one_right ha1sq
  have hb1inv_eq : b1⁻¹ = b1 := inv_eq_of_mul_eq_one_right hb1sq
  have ha1mem : a1⁻¹ * a ∈ V1 := by
    rw [ha1]
    have h : (a * φ u)⁻¹ * a = (φ u)⁻¹ := by group
    rw [h, hφ.inv_eq' hu]
    exact hφ.mem u hu
  have hb1mem : b1⁻¹ * b ∈ V1 := by
    rw [hb1]
    have h : (b * φ w)⁻¹ * b = (φ w)⁻¹ := by group
    rw [h, hφ.inv_eq' hw]
    exact hφ.mem w hw
  have ha1act : ∀ v : Fin 5 → ZMod 2, IsEvenVec v →
      a1 * φ v * a1⁻¹ = φ (permVec s8Pa v) := by
    intro v hv
    rw [ha1]
    have hconj : φ u * φ v * (φ u)⁻¹ = φ v := by
      rw [hφ.comm' hu hv, mul_assoc, mul_inv_cancel, mul_one]
    calc (a * φ u) * φ v * (a * φ u)⁻¹
        = a * (φ u * φ v * (φ u)⁻¹) * a⁻¹ := by group
      _ = a * φ v * a⁻¹ := by rw [hconj]
      _ = φ (permVec s8Pa v) := ha v hv
  have hb1act : ∀ v : Fin 5 → ZMod 2, IsEvenVec v →
      b1 * φ v * b1⁻¹ = φ (permVec s8Pb v) := by
    intro v hv
    rw [hb1]
    have hconj : φ w * φ v * (φ w)⁻¹ = φ v := by
      rw [hφ.comm' hw hv, mul_assoc, mul_inv_cancel, mul_one]
    calc (b * φ w) * φ v * (b * φ w)⁻¹
        = b * (φ w * φ v * (φ w)⁻¹) * b⁻¹ := by group
      _ = b * φ v * b⁻¹ := by rw [hconj]
      _ = φ (permVec s8Pb v) := hb v hv
  set c : H := a1 * b1 * a1⁻¹ * b1⁻¹ with hc
  have hcV : c ∈ V1 := by
    have hqa : (a1 : H ⧸ V1) = (a : H ⧸ V1) := (QuotientGroup.eq (s := V1)).mpr ha1mem
    have hqb : (b1 : H ⧸ V1) = (b : H ⧸ V1) := (QuotientGroup.eq (s := V1)).mpr hb1mem
    have h2 : ((a * b * a⁻¹ * b⁻¹ : H) : H ⧸ V1) = 1 :=
      (QuotientGroup.eq_one_iff (N := V1) (a * b * a⁻¹ * b⁻¹)).mpr hab
    rw [← (QuotientGroup.eq_one_iff (N := V1) c), hc]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hqa, hqb]
    simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h2
  obtain ⟨r, hr, hrc⟩ := hφ.surj c hcV
  have hc_eq : c = a1 * b1 * a1 * b1 := by
    rw [hc, ha1inv_eq, hb1inv_eq]
  have hcinv_eq : c⁻¹ = b1 * a1 * b1 * a1 := by
    rw [hc_eq]
    simp only [mul_inv_rev, ha1inv_eq, hb1inv_eq, mul_assoc]
  have hcinv : c⁻¹ = c := by
    rw [← hrc, hφ.inv_eq' hr]
  have haca : a1 * c * a1⁻¹ = c := by
    have h : a1 * c * a1⁻¹ = c⁻¹ := by
      calc a1 * c * a1⁻¹ = a1 * (a1 * b1 * a1 * b1) * a1 := by rw [hc_eq, ha1inv_eq]
        _ = (a1 * a1) * b1 * a1 * b1 * a1 := by group
        _ = b1 * a1 * b1 * a1 := by rw [ha1sq]; group
        _ = c⁻¹ := by rw [hcinv_eq]
    rw [h, hcinv]
  have hbcb : b1 * c * b1⁻¹ = c := by
    have h : b1 * c * b1⁻¹ = c⁻¹ := by
      calc b1 * c * b1⁻¹ = b1 * (a1 * b1 * a1 * b1) * b1 := by rw [hc_eq, hb1inv_eq]
        _ = b1 * a1 * b1 * a1 * (b1 * b1) := by group
        _ = b1 * a1 * b1 * a1 := by rw [hb1sq]; group
        _ = c⁻¹ := by rw [hcinv_eq]
    rw [h, hcinv]
  have hra : permVec s8Pa r = r :=
    hφ.eq_of_eq' (s8_isEvenVec_permVec s8Pa hr) hr (by
      rw [← ha1act r hr, hrc]
      exact haca)
  have hrb : permVec s8Pb r = r :=
    hφ.eq_of_eq' (s8_isEvenVec_permVec s8Pb hr) hr (by
      rw [← hb1act r hr, hrc]
      exact hbcb)
  obtain ⟨z, hz, hzfix, hzr⟩ := s8_fin_free_ab' r hr hra hrb
  have hb'mem : (b1 * φ z)⁻¹ * b ∈ V1 := by
    have h : (b1 * φ z)⁻¹ * b = (φ z)⁻¹ * (b1⁻¹ * b) := by group
    rw [h]
    exact V1.mul_mem (V1.inv_mem (hφ.mem z hz)) hb1mem
  have hbz : b1 * φ z * b1 = φ z := by
    have h := hb1act z hz
    rw [hb1inv_eq, hzfix] at h
    exact h
  have hb'sq : (b1 * φ z) * (b1 * φ z) = 1 := by
    calc (b1 * φ z) * (b1 * φ z) = (b1 * φ z * b1) * φ z := by group
      _ = φ z * φ z := by rw [hbz]
      _ = 1 := hφ.mul_self' hz
  have hb1rinv : b1⁻¹ * φ r * b1 = φ r := by
    rw [hb1inv_eq]
    have h := hb1act r hr
    rw [hb1inv_eq, hrb] at h
    exact h
  have hb1phi : φ r * b1 = b1 * φ r := by
    calc φ r * b1 = b1 * (b1⁻¹ * φ r * b1) := by group
      _ = b1 * φ r := by rw [hb1rinv]
  have hcb1 : a1 * b1 * a1⁻¹ = c * b1 := by
    calc a1 * b1 * a1⁻¹ = a1 * b1 * a1 := by rw [ha1inv_eq]
      _ = a1 * b1 * a1 * (b1 * b1) := by rw [hb1sq, mul_one]
      _ = (a1 * b1 * a1 * b1) * b1 := by group
      _ = c * b1 := by rw [← hc_eq]
  have hrp : r + permVec s8Pa z = z := by
    rw [hzr, add_assoc z (permVec s8Pa z) (permVec s8Pa z),
      s8_add_self (permVec s8Pa z), add_zero]
  have ha'b' : a1 * (b1 * φ z) * a1⁻¹ = b1 * φ z := by
    calc a1 * (b1 * φ z) * a1⁻¹
        = (a1 * b1 * a1⁻¹) * (a1 * φ z * a1⁻¹) := by group
      _ = (c * b1) * φ (permVec s8Pa z) := by rw [hcb1, ha1act z hz]
      _ = (φ r * b1) * φ (permVec s8Pa z) := by rw [← hrc]
      _ = b1 * (φ r * φ (permVec s8Pa z)) := by rw [hb1phi]; group
      _ = b1 * φ (r + permVec s8Pa z) := by
        rw [← hφ.mul r (permVec s8Pa z) hr (s8_isEvenVec_permVec s8Pa hz)]
      _ = b1 * φ z := by rw [hrp]
  refine ⟨a1, b1 * φ z, ha1mem, hb'mem, ha1sq, hb'sq, ?_⟩
  exact mul_inv_eq_iff_eq_mul.mp ha'b'

end CFSG.OddStandard.SmallF3.Omega
