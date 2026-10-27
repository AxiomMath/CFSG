module

public import Certificates.Data.Kernel.PermCent.F7CentChk
public import CFSG.Certificates.Kernel.PermCent.F7CentSound
public import CFSG.Certificates.Kernel.PermCent.F7Conj
public import CFSG.GH74.GLS.C3.Prop121.Card7F3Inputs

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv Equiv.Perm CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7 CFSG.GH74.GLS.C3.Prop121.Card7.FF CFSG.Certificates.Kernel.F7Conj

@[expose] def RelP (c : F7) (x : CV 7 × CV 4) : Prop := (c : Amb 7) = evF7 x

theorem forall2_of_map {L : List F7} {Lp : List (CV 7 × CV 4)}
    (h : L.map Subtype.val = Lp.map evF7) : List.Forall₂ RelP L Lp := by
  induction L generalizing Lp with
  | nil =>
    cases Lp with
    | nil => exact .nil
    | cons _ _ => simp at h
  | cons a L ih =>
    cases Lp with
    | nil => simp at h
    | cons x Lp =>
      simp only [List.map_cons, List.cons.injEq] at h
      exact .cons h.1 (ih h.2)

section Forall2

variable {α β γ δ : Type*} {R : α → β → Prop} {S : γ → δ → Prop}

theorem f2_filter {L : List α} {Lp : List β} (h : List.Forall₂ R L Lp) {P : α → Bool} {Q : β → Bool}
    (hPQ : ∀ a b, R a b → P a = Q b) : List.Forall₂ R (L.filter P) (Lp.filter Q) := by
  induction h with
  | nil => exact .nil
  | @cons a b l m hab _ ih =>
    rw [List.filter_cons, List.filter_cons, hPQ a b hab]
    split
    · exact .cons hab ih
    · exact ih

theorem f2_countP {L : List α} {Lp : List β} (h : List.Forall₂ R L Lp) {P : α → Bool}
    {Q : β → Bool} (hPQ : ∀ a b, R a b → P a = Q b) : L.countP P = Lp.countP Q := by
  induction h with
  | nil => rfl
  | @cons a b l m hab _ ih => rw [List.countP_cons, List.countP_cons, hPQ a b hab, ih]

theorem f2_all {L : List α} {Lp : List β} (h : List.Forall₂ R L Lp) {P : α → Bool}
    {Q : β → Bool} (hPQ : ∀ a b, R a b → P a = Q b) : L.all P = Lp.all Q := by
  induction h with
  | nil => rfl
  | @cons a b l m hab _ ih => rw [List.all_cons, List.all_cons, hPQ a b hab, ih]

theorem f2_append {L L' : List α} {Lp Lp' : List β} (h : List.Forall₂ R L Lp)
    (h' : List.Forall₂ R L' Lp') : List.Forall₂ R (L ++ L') (Lp ++ Lp') := by
  induction h with
  | nil => exact h'
  | cons hab _ ih => exact .cons hab ih

theorem cons_sprod (a : α) (l : List α) (m : List γ) :
    (a :: l) ×ˢ m = m.map (Prod.mk a) ++ l ×ˢ m := by
  first
    | rfl
    | simp [SProd.sprod, List.product]

theorem f2_product {L : List α} {Lp : List β} {M : List γ} {Mp : List δ} (h : List.Forall₂ R L Lp)
    (h' : List.Forall₂ S M Mp) :
    List.Forall₂ (fun p q => R p.1 q.1 ∧ S p.2 q.2) (L ×ˢ M) (Lp ×ˢ Mp) := by
  induction h with
  | nil => exact .nil
  | @cons a b l m hab _ ih =>
    rw [cons_sprod, cons_sprod]
    refine f2_append ?_ ih
    clear ih
    induction h' with
    | nil => exact .nil
    | cons hcd _ ih' => exact .cons ⟨hab, hcd⟩ ih'

end Forall2

theorem evF7_mul (x y : CV 7 × CV 4) : evF7 x * evF7 y = evF7 (x.1 * y.1, x.2 * y.2) := by
  simp only [evF7, Prod.mk_mul_mk, ev_mul']

theorem evF7_pow (x : CV 7 × CV 4) (n : ℕ) : evF7 x ^ n = evF7 (x.1 ^ n, x.2 ^ n) := by
  simp only [evF7, Prod.pow_mk, ev_pow']

theorem evF7_eq_iff (x y : CV 7 × CV 4) : evF7 x = evF7 y ↔ x.1 = y.1 ∧ x.2 = y.2 := by
  simp only [evF7, Prod.mk.injEq, ev_eq_iff]

theorem evF7_one : evF7 (1, 1) = 1 := by
  simp only [evF7, ev_one]
  rfl

theorem val_eq_iff (a b : F7) : a = b ↔ (a : Amb 7) = (b : Amb 7) := Subtype.ext_iff

theorem decide_inv {c : F7} {x : CV 7 × CV 4} (h : RelP c x) (n : ℕ) :
    decide (IsInv c ∧ nm7 (c : Amb 7) = n) = invP x n := by
  unfold invP IsInv
  apply decide_eq_decide.2
  have h2 : c ^ 2 = 1 ↔ x.1 * x.1 = 1 ∧ x.2 * x.2 = 1 := by
    rw [val_eq_iff, val_pow, h, OneMemClass.coe_one, ← evF7_one, evF7_pow, evF7_eq_iff, pow_two,
      pow_two]
  have h1 : c ≠ 1 ↔ ¬ (x.1 = 1 ∧ x.2 = 1) := by
    rw [ne_eq, val_eq_iff, h, OneMemClass.coe_one, ← evF7_one, evF7_eq_iff]
  rw [h2, h1, h]
  rfl

theorem decide_XF {c : F7} {x : CV 7 × CV 4} (h : RelP c x) : decide (XF c) = invP x 4 :=
  decide_inv h 4

theorem decide_YF {c : F7} {x : CV 7 × CV 4} (h : RelP c x) : decide (YF c) = invP x 8 :=
  decide_inv h 8

theorem decide_comm {c b : F7} {x y : CV 7 × CV 4} (hc : RelP c x) (hb : RelP b y) :
    decide (c * b = b * c) = commP x y := by
  unfold commP
  rw [eq22C_eq, eq22C_eq, ← Bool.decide_and]
  apply decide_eq_decide.2
  rw [val_eq_iff, val_mul, val_mul, hc, hb, evF7_mul, evF7_mul, evF7_eq_iff]

theorem decide_pow {c b z : F7} {x y w : CV 7 × CV 4} (hc : RelP c x) (hb : RelP b y)
    (hz : RelP z w) (n : ℕ) : decide ((c * b) ^ n = z) = powP x y n w := by
  unfold powP
  apply decide_eq_decide.2
  rw [val_eq_iff, val_pow, val_mul, hc, hb, hz, evF7_mul, evF7_pow, evF7_eq_iff]

theorem relP_one : RelP 1 (1, 1) := evF7_one.symm

theorem relP_x0F : RelP x0F (1, cOf x4) := by
  unfold RelP evF7 x0F x0
  simp only [ev_one, ev_cOf]

theorem ccardB_eq_countP (u b : F7) :
    ccardB u b = (CL u).countP fun c => decide (c * b = b * c) := by
  unfold ccardB CL
  rw [List.countP_filter]
  apply List.countP_congr
  intro c _
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact and_comm

theorem ccardB_eq_cntP {u b : F7} {L : List (CV 7 × CV 4)} {y : CV 7 × CV 4}
    (hL : List.Forall₂ RelP (CL u) L) (hb : RelP b y) : ccardB u b = cntP L y := by
  rw [ccardB_eq_countP]
  exact f2_countP hL fun c x hc => decide_comm hc hb

theorem forall2_CL (u : F7) (ρ : Perm (Fin 7)) (hu : (u : Amb 7) = (ρ, 1)) :
    List.Forall₂ RelP (CL u) (CF7 (cOf ρ)) :=
  forall2_of_map (map_filter_comm u ρ hu)

end CFSG.Certificates.Kernel.PkCV

end
