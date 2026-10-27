module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Setup

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {L J Py P : Subgroup G} {a w : G}

theorem Setup.hxa (hs : Setup G x y L J a Py P w) : x * a = a * x := hs.hFB.hax.symm

theorem Setup.hay (hs : Setup G x y L J a Py P w) : a * y = y * a :=
  mem_centralizer_singleton_iff.mp (hs.hFB.cfg.hJ.1.1 hs.hFB.ha)

theorem Setup.haP (hs : Setup G x y L J a Py P w) : a ∈ P := hs.hPyP hs.haPy

theorem Setup.hww (hs : Setup G x y L J a Py P w) : w * w = x :=
  mul_self_eq_of_orderOf_four hs.hFB.cfg.hL hs.hFB.cfg.hx hs.hwP.2 hs.hw4

theorem Setup.hL' (hs : Setup G x y L J a Py P w) : IsIntrinsic x (conjugate L a) :=
  isIntrinsic_conjugate hs.hxa hs.hFB.cfg.hL

theorem Setup.hL'cSec (hs : Setup G x y L J a Py P w) : conjugate L a ≤ cSec L :=
  conjugate_le_cSec hs.hxa hs.hFB.cfg.hL hs.hFB.haL

theorem Setup.hwa_mem (hs : Setup G x y L J a Py P w) : a⁻¹ * w * a ∈ conjugate L a := by
  rw [mem_conjugate_iff', show a * (a⁻¹ * w * a) * a⁻¹ = w by group]
  exact hs.hwP.2

theorem Setup.hwa_P (hs : Setup G x y L J a Py P w) : a⁻¹ * w * a ∈ P :=
  mul_mem (mul_mem (inv_mem hs.haP) hs.hwP.1) hs.haP

theorem Setup.hwa_sq (hs : Setup G x y L J a Py P w) : (a⁻¹ * w * a) * (a⁻¹ * w * a) = x := by
  calc (a⁻¹ * w * a) * (a⁻¹ * w * a) = a⁻¹ * (w * w) * a := by group
    _ = a⁻¹ * x * a := by rw [hs.hww]
    _ = a⁻¹ * (x * a) := by group
    _ = a⁻¹ * (a * x) := by rw [hs.hxa]
    _ = x := by group

theorem Setup.hwwa (hs : Setup G x y L J a Py P w) : w * (a⁻¹ * w * a) = (a⁻¹ * w * a) * w := by
  have hcs : a⁻¹ * w * a ∈ cSec L := hs.hL'cSec hs.hwa_mem
  have h1 : ⁅w, a⁻¹ * w * a⁆ ∈ pPrimeCoreOf 2 L := hcs.2.2 w hs.hwP.2
  have h2 : ⁅w, a⁻¹ * w * a⁆ ∈ P := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hs.hwP.1 hs.hwa_P) (inv_mem hs.hwP.1)) (inv_mem hs.hwa_P)
  have h3 := eq_one_of_mem_pPrimeCoreOf h1 (isPGroup_zpowers_of_mem hs.hP.2.1 h2)
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem Setup.huu (hs : Setup G x y L J a Py P w) :
    (w * (a⁻¹ * w * a)) * (w * (a⁻¹ * w * a)) = 1 := by
  have hc := hs.hwwa
  calc (w * (a⁻¹ * w * a)) * (w * (a⁻¹ * w * a))
      = w * ((a⁻¹ * w * a) * w) * (a⁻¹ * w * a) := by group
    _ = w * (w * (a⁻¹ * w * a)) * (a⁻¹ * w * a) := by rw [← hc]
    _ = (w * w) * ((a⁻¹ * w * a) * (a⁻¹ * w * a)) := by group
    _ = x * x := by rw [hs.hww, hs.hwa_sq]
    _ = 1 := mul_self_eq_one_of_orderOf_eq_two hs.hFB.cfg.hx

theorem Setup.hu_ne (hs : Setup G x y L J a Py P w) (h44 : II4_44) : w * (a⁻¹ * w * a) ≠ 1 := by
  intro h1
  have hwL' : w ∈ conjugate L a := by
    have : w = (a⁻¹ * w * a)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_mem hs.hwa_mem
  have hF := eq_one_or_eq_of_mem_inf_conjugate h44 hs.hFB.cfg.simple hs.hFB.cfg.hx hs.hxa
    hs.hFB.cfg.hL hs.hFB.haL hs.hwP.2 hwL' (isPGroup_zpowers_of_mem hs.hP.2.1 hs.hwP.1)
  have h4 := hs.hw4
  rcases hF with h | h
  · rw [h] at h4
    simp at h4
  · rw [h, hs.hFB.cfg.hx] at h4
    norm_num at h4

theorem Setup.hu2 (hs : Setup G x y L J a Py P w) (h44 : II4_44) :
    orderOf (w * (a⁻¹ * w * a)) = 2 :=
  orderOf_eq_two_of_mul_self_eq_one hs.huu (hs.hu_ne h44)

theorem Setup.hu_cx (hs : Setup G x y L J a Py P w) :
    w * (a⁻¹ * w * a) ∈ centralizer ({x} : Set G) :=
  mul_mem (hs.hFB.cfg.hL.1.1 hs.hwP.2) (hs.hL'.1.1 hs.hwa_mem)

theorem Setup.hu_cy (hs : Setup G x y L J a Py P w) :
    w * (a⁻¹ * w * a) ∈ centralizer ({y} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  have hya : y * a = a * y := hs.hay.symm
  have hya' : y * a⁻¹ = a⁻¹ * y := by
    calc y * a⁻¹ = a⁻¹ * (a * y) * a⁻¹ := by group
      _ = a⁻¹ * (y * a) * a⁻¹ := by rw [hya]
      _ = a⁻¹ * y := by group
  have hya'' : a * y⁻¹ = y⁻¹ * a := by
    calc a * y⁻¹ = y⁻¹ * (y * a) * y⁻¹ := by group
      _ = y⁻¹ * (a * y) * y⁻¹ := by rw [hya]
      _ = y⁻¹ * a := by group
  have h1 : y * w * y⁻¹ = w⁻¹ := hs.hwinv
  have h2 : y * (a⁻¹ * w * a) * y⁻¹ = (a⁻¹ * w * a)⁻¹ := by
    calc y * (a⁻¹ * w * a) * y⁻¹ = (y * a⁻¹) * w * (a * y⁻¹) := by group
      _ = (a⁻¹ * y) * w * (y⁻¹ * a) := by rw [hya', hya'']
      _ = a⁻¹ * (y * w * y⁻¹) * a := by group
      _ = a⁻¹ * w⁻¹ * a := by rw [h1]
      _ = (a⁻¹ * w * a)⁻¹ := by group
  have h3 : y * (w * (a⁻¹ * w * a)) * y⁻¹ = w * (a⁻¹ * w * a) := by
    calc y * (w * (a⁻¹ * w * a)) * y⁻¹
        = (y * w * y⁻¹) * (y * (a⁻¹ * w * a) * y⁻¹) := by group
      _ = w⁻¹ * (a⁻¹ * w * a)⁻¹ := by rw [h1, h2]
      _ = ((a⁻¹ * w * a) * w)⁻¹ := by group
      _ = (w * (a⁻¹ * w * a))⁻¹ := by rw [← hs.hwwa]
      _ = w * (a⁻¹ * w * a) := inv_eq_of_mul_eq_one_right hs.huu
  calc w * (a⁻¹ * w * a) * y = (y * (w * (a⁻¹ * w * a)) * y⁻¹) * y := by rw [h3]
    _ = y * (w * (a⁻¹ * w * a)) := by group

theorem Setup.hu_N (hs : Setup G x y L J a Py P w) :
    w * (a⁻¹ * w * a) ∈ normalizer (L : Set G) :=
  mul_mem (le_normalizer hs.hwP.2) (hs.hL'cSec hs.hwa_mem).1

theorem Setup.hu_P (hs : Setup G x y L J a Py P w) : w * (a⁻¹ * w * a) ∈ P :=
  mul_mem hs.hwP.1 hs.hwa_P

theorem Setup.hb_formula (hs : Setup G x y L J a Py P w) :
    (w * (a⁻¹ * w * a))⁻¹ * a⁻¹ * (w * (a⁻¹ * w * a)) * a = w⁻¹ * (a⁻¹ * a⁻¹ * w * a * a) := by
  have hc : Commute w (a⁻¹ * w * a) := hs.hwwa
  have hc' : w⁻¹ * (a⁻¹ * w * a) = (a⁻¹ * w * a) * w⁻¹ := (Commute.inv_left hc).eq
  calc (w * (a⁻¹ * w * a))⁻¹ * a⁻¹ * (w * (a⁻¹ * w * a)) * a
      = (a⁻¹ * w * a)⁻¹ * (w⁻¹ * (a⁻¹ * w * a)) * (a⁻¹ * (a⁻¹ * w * a) * a) := by group
    _ = (a⁻¹ * w * a)⁻¹ * ((a⁻¹ * w * a) * w⁻¹) * (a⁻¹ * (a⁻¹ * w * a) * a) := by rw [hc']
    _ = w⁻¹ * (a⁻¹ * a⁻¹ * w * a * a) := by group

theorem Setup.hb_mem_L (hs : Setup G x y L J a Py P w) : w⁻¹ * (a⁻¹ * a⁻¹ * w * a * a) ∈ L := by
  have h1 : a⁻¹ * a⁻¹ * w * a * a ∈ L := by
    have := (mem_normalizer_iff.mp (inv_mem hs.a2N) w).mp hs.hwP.2
    rwa [show (a * a)⁻¹ * w * (a * a)⁻¹⁻¹ = a⁻¹ * a⁻¹ * w * a * a by
      simp only [mul_inv_rev, inv_inv, mul_assoc]] at this
  exact mul_mem (inv_mem hs.hwP.2) h1

theorem Setup.hb_mem_P (hs : Setup G x y L J a Py P w) : w⁻¹ * (a⁻¹ * a⁻¹ * w * a * a) ∈ P :=
  mul_mem (inv_mem hs.hwP.1) (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hs.haP)
    (inv_mem hs.haP)) hs.hwP.1) hs.haP) hs.haP)

theorem Setup.hb_ne_one (hs : Setup G x y L J a Py P w) : w⁻¹ * (a⁻¹ * a⁻¹ * w * a * a) ≠ 1 := by
  intro h1
  have hz := inv_mul_eq_one.mp h1
  have e : a * a * (a⁻¹ * a⁻¹ * w * a * a) = w * (a * a) := by group
  rw [← hz] at e
  have hcom : Commute w (a * a) := e.symm
  obtain ⟨m, hm2, -, hyp⟩ := hs.hFB.exists_pow
  have hy2 : y = (a * a) ^ (2 ^ (m - 2)) := by
    rw [hyp, ← pow_two, ← pow_mul]
    congr 1
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
    ring
  have hcy : Commute w y := by
    rw [hy2]
    exact hcom.pow_right _
  have h2 : y * w * y⁻¹ = w := by
    have : y * w = w * y := hcy.symm.eq
    calc y * w * y⁻¹ = w * y * y⁻¹ := by rw [this]
      _ = w := by group
  have hww : w = w⁻¹ := by rw [← hs.hwinv, h2]
  have hw2 : w * w = 1 := mul_eq_one_iff_eq_inv.mpr hww
  have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
  have h4 := hs.hw4
  rw [h4] at hdvd
  norm_num at hdvd

theorem Setup.hx_mem_zpowers_b (hs : Setup G x y L J a Py P w) :
    x ∈ zpowers (w⁻¹ * (a⁻¹ * a⁻¹ * w * a * a)) :=
  hs.hFB.cfg.hL.mem_zpowers_of_isPGroup hs.hFB.cfg.hx hs.hb_mem_L
    (isPGroup_zpowers_of_mem hs.hP.2.1 hs.hb_mem_P) hs.hb_ne_one

theorem Setup.hu_not_mem_normalizer_J (hs : Setup G x y L J a Py P w) :
    w * (a⁻¹ * w * a) ∉ normalizer (J : Set G) := by
  intro huJ
  have hbJ : (w * (a⁻¹ * w * a))⁻¹ * a⁻¹ * (w * (a⁻¹ * w * a)) * a ∈ J := by
    have h1 := (mem_normalizer_iff.mp (inv_mem huJ) a⁻¹).mp (inv_mem hs.hFB.ha)
    rw [inv_inv] at h1
    exact mul_mem h1 hs.hFB.ha
  rw [hs.hb_formula] at hbJ
  have hxJ' : x ∈ J := (zpowers_le.mpr hbJ) hs.hx_mem_zpowers_b
  exact hs.hFB.x_ne_y (hs.hFB.cfg.hJ.eq_of_involution hs.hFB.cfg.hy hxJ' hs.hFB.cfg.hx)

end CFSG.GH74.GLS.Stage1.Thm2.Recip
