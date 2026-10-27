module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Elem
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section ModD

variable {G : Type} [Group G] {V D : Subgroup G}

theorem sq_mem_of_mul_mem (hVD : ∀ v ∈ V, v ∈ normalizer (D : Set G)) {x a : G} (hx : x ∈ V)
    (h1 : x * a ∈ D) (h2 : x * a⁻¹ ∈ D) : a * a ∈ D := by
  have h3 : (x * a) * (x * a⁻¹)⁻¹ ∈ D := mul_mem h1 (inv_mem h2)
  have h4 : x⁻¹ * ((x * a) * (x * a⁻¹)⁻¹) * x⁻¹⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (hVD x⁻¹ (inv_mem hx)) _).mp h3
  have e : x⁻¹ * ((x * a) * (x * a⁻¹)⁻¹) * x⁻¹⁻¹ = a * a := by group
  rwa [e] at h4

theorem mem_of_sq_mem {a : G} (hodd : Odd (orderOf a)) (h : a * a ∈ D) : a ∈ D := by
  obtain ⟨m, hm⟩ := hodd
  have hpow : a ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one a
  have hbm : a = (a * a) ^ (m + 1) := by
    calc a = a ^ (2 * m + 1) * a := by rw [hpow, one_mul]
      _ = (a * a) ^ (m + 1) := by rw [← pow_succ, ← pow_two, ← pow_mul]; ring_nf
  have h2 := Subgroup.pow_mem D h (m + 1)
  rwa [← hbm] at h2

theorem lift_fixed {t : G} (ht : t * t = 1) (hDV : D ≤ V) (hVD : ∀ v ∈ V, v ∈ normalizer (D : Set G))
    (hodd : ∀ d ∈ D, Odd (orderOf d)) {v : G} (hv : v ∈ V) (hfix : t * v * t⁻¹ * v⁻¹ ∈ D) :
    ∃ u ∈ V, v⁻¹ * u ∈ D ∧ t * u * t⁻¹ = u := by
  set w : G := v⁻¹ * (t * v * t⁻¹) with hw
  have hwD : w ∈ D := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hVD v⁻¹ (inv_mem hv)) _).mp hfix
    have e : v⁻¹ * (t * v * t⁻¹ * v⁻¹) * v⁻¹⁻¹ = w := by rw [hw]; group
    rwa [e] at h1
  have htw : t * w * t⁻¹ = w⁻¹ := by
    have hc := conj_conj_of_mul_self ht v
    rw [hw]
    calc t * (v⁻¹ * (t * v * t⁻¹)) * t⁻¹ = (t * v * t⁻¹)⁻¹ * (t * (t * v * t⁻¹) * t⁻¹) := by group
      _ = (t * v * t⁻¹)⁻¹ * v := by rw [hc]
      _ = (v⁻¹ * (t * v * t⁻¹))⁻¹ := by group
  obtain ⟨m, hm⟩ := hodd w hwD
  have hpow : w ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  set a : G := w ^ (m + 1) with ha
  have haa : a * a = w := by
    calc a * a = w ^ (m + 1) * w ^ (m + 1) := by rw [ha]
      _ = w ^ ((m + 1) + (m + 1)) := (pow_add w (m + 1) (m + 1)).symm
      _ = w ^ (2 * m + 1) * w := by rw [← pow_succ]; ring_nf
      _ = w := by rw [hpow, one_mul]
  have haD : a ∈ D := Subgroup.pow_mem D hwD _
  have hta : t * a * t⁻¹ = a⁻¹ := by
    rw [ha, ← conj_pow, htw, inv_pow]
  have htv : t * v * t⁻¹ = v * w := by rw [hw]; group
  refine ⟨v * a, mul_mem hv (hDV haD), ?_, ?_⟩
  · rw [inv_mul_cancel_left]
    exact haD
  · calc t * (v * a) * t⁻¹ = (t * v * t⁻¹) * (t * a * t⁻¹) := by group
      _ = (v * w) * a⁻¹ := by rw [htv, hta]
      _ = v * (a * a) * a⁻¹ := by rw [haa]
      _ = v * a := by group

@[expose] def invModSub (V D : Subgroup G) (z : G) (hz : z ∈ normalizer (V : Set G)) (hVV : ⁅V, V⁆ ≤ D)
    (hVD : ∀ v ∈ V, v ∈ normalizer (D : Set G)) : Subgroup G where
  carrier := {v | v ∈ V ∧ z * v * z⁻¹ * v ∈ D}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨haV, ha⟩ ⟨hbV, hb⟩
    have ha'V : z * a * z⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hz a).mp haV
    have hb'V : z * b * z⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hz b).mp hbV
    refine ⟨mul_mem haV hbV, ?_⟩
    have hc : ⁅z * b * z⁻¹, a⁆ ∈ D := hVV (Subgroup.commutator_mem_commutator hb'V haV)
    have h1 : (z * a * z⁻¹) * ⁅z * b * z⁻¹, a⁆ * (z * a * z⁻¹)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hVD _ ha'V) _).mp hc
    have e : z * (a * b) * z⁻¹ * (a * b) = ((z * a * z⁻¹) * ⁅z * b * z⁻¹, a⁆ * (z * a * z⁻¹)⁻¹) *
        ((z * a * z⁻¹) * a) * ((z * b * z⁻¹) * b) := by
      simp only [commutatorElement_def]
      group
    show z * (a * b) * z⁻¹ * (a * b) ∈ D
    rw [e]
    exact mul_mem (mul_mem h1 ha) hb
  inv_mem' := by
    rintro a ⟨haV, ha⟩
    refine ⟨inv_mem haV, ?_⟩
    have h1 : a * ((z * a * z⁻¹) * a) * a⁻¹ ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (hVD a haV) _).mp ha
      simpa using this
    have e : z * a⁻¹ * z⁻¹ * a⁻¹ = (a * (z * a * z⁻¹))⁻¹ := by group
    have e2 : a * ((z * a * z⁻¹) * a) * a⁻¹ = a * (z * a * z⁻¹) := by group
    show z * a⁻¹ * z⁻¹ * a⁻¹ ∈ D
    rw [e]
    rw [e2] at h1
    exact inv_mem h1

theorem mem_invModSub {z : G} {hz : z ∈ normalizer (V : Set G)} {hVV : ⁅V, V⁆ ≤ D}
    {hVD : ∀ v ∈ V, v ∈ normalizer (D : Set G)} {v : G} :
    v ∈ invModSub V D z hz hVV hVD ↔ v ∈ V ∧ z * v * z⁻¹ * v ∈ D := Iff.rfl

theorem comm_acts_trivially {t c : G} (ht : t * t = 1) (hVD : ∀ v ∈ V, v ∈ normalizer (D : Set G))
    (hT : ∀ y ∈ V, y * (t * y * t⁻¹) ∈ D) (htV : t ∈ normalizer (V : Set G)) (htD : t ∈ normalizer (D : Set G))
    (hcV : c ∈ normalizer (V : Set G)) (hcD : c ∈ normalizer (D : Set G)) {x : G} (hx : x ∈ V) :
    x⁻¹ * (⁅c, t⁆ * x * ⁅c, t⁆⁻¹) ∈ D := by
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hcV' : c⁻¹ ∈ normalizer (V : Set G) := inv_mem hcV
  have hcD' : c⁻¹ ∈ normalizer (D : Set G) := inv_mem hcD
  have ha₁V : t⁻¹ * x * t ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem htV) x).mp hx
    simpa using this
  have h1 : x * (t⁻¹ * x * t) ∈ D := by
    have := hT x hx
    rw [htt] at this ⊢
    exact this
  have hwV : c⁻¹ * x * c ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp hcV' x).mp hx
    simpa using this
  have ha₂V : c⁻¹ * (t⁻¹ * x * t) * c ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp hcV' _).mp ha₁V
    simpa using this
  have h2 : (c⁻¹ * x * c) * (c⁻¹ * (t⁻¹ * x * t) * c) ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp hcD' _).mp h1
    have e : c⁻¹ * (x * (t⁻¹ * x * t)) * c⁻¹⁻¹ = (c⁻¹ * x * c) * (c⁻¹ * (t⁻¹ * x * t) * c) := by group
    rwa [e] at this
  have h3 : (c⁻¹ * x * c) * (t * (c⁻¹ * x * c) * t⁻¹) ∈ D := hT _ hwV
  have h4 : (t * (c⁻¹ * x * c) * t⁻¹) * (t * (c⁻¹ * (t⁻¹ * x * t) * c) * t⁻¹) ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp htD _).mp h2
    have e : t * ((c⁻¹ * x * c) * (c⁻¹ * (t⁻¹ * x * t) * c)) * t⁻¹ =
        (t * (c⁻¹ * x * c) * t⁻¹) * (t * (c⁻¹ * (t⁻¹ * x * t) * c) * t⁻¹) := by group
    rwa [e] at this
  have hrV : t * (c⁻¹ * x * c) * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp htV _).mp hwV
  have h5 : (c⁻¹ * x * c)⁻¹ * (t * (c⁻¹ * (t⁻¹ * x * t) * c) * t⁻¹) ∈ D := by
    set w : G := c⁻¹ * x * c with hw
    set r : G := t * w * t⁻¹ with hr
    set a₃ : G := t * (c⁻¹ * (t⁻¹ * x * t) * c) * t⁻¹ with ha₃
    have hrw : r * w ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (hVD w⁻¹ (inv_mem hwV)) _).mp h3
      have e : w⁻¹ * (w * r) * w⁻¹⁻¹ = r * w := by group
      rwa [e] at this
    have e : w⁻¹ * a₃ = (r * w)⁻¹ * (r * a₃) := by group
    rw [e]
    exact mul_mem (inv_mem hrw) h4
  have h6 := (Subgroup.mem_normalizer_iff.mp hcD _).mp h5
  have e : c * ((c⁻¹ * x * c)⁻¹ * (t * (c⁻¹ * (t⁻¹ * x * t) * c) * t⁻¹)) * c⁻¹ =
      x⁻¹ * (⁅c, t⁆ * x * ⁅c, t⁆⁻¹) := by
    simp only [commutatorElement_def]
    group
  rwa [e] at h6

theorem commutator_mem_of_cong (hVD : ∀ v ∈ V, v ∈ normalizer (D : Set G)) {x g : G} (hx : x ∈ V)
    (h : x⁻¹ * (g * x * g⁻¹) ∈ D) : ⁅x, g⁆ ∈ D := by
  have h1 : x * (x⁻¹ * (g * x * g⁻¹))⁻¹ * x⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (hVD x hx) _).mp (inv_mem h)
  have e : x * (x⁻¹ * (g * x * g⁻¹))⁻¹ * x⁻¹ = ⁅x, g⁆ := by
    simp only [commutatorElement_def]
    group
  rwa [e] at h1

end ModD

end CFSG.GH74.GLS.Stage2.Bender.Thm2
