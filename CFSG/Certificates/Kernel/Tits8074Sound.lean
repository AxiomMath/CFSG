module

public import Certificates.Data.Kernel.Tits8074
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Nat.Defs

public section

namespace CFSG.KC.Tits8074

open Equiv

@[expose] def LRep (L : Nat → Nat) (g : Nat → Perm (Fin 1755)) : Prop :=
  (∀ c < 24, ∀ x : Fin 1755, ap L c x = (g c x : Nat)) ∧ ∀ c < 24, g (Nat.xor c 1) = (g c)⁻¹

@[expose] def wv (g : Nat → Perm (Fin 1755)) (w : List Nat) : Perm (Fin 1755) := (w.map g).prod

@[expose] def xb (g : Nat → Perm (Fin 1755)) (z : Nat) (t : List Nat) : Perm (Fin 1755) :=
  wv g t * g z * (wv g t)⁻¹ * g 2

variable {L : Nat → Nat} {g : Nat → Perm (Fin 1755)}

theorem xor_lt {c : Nat} (h : c < 24) : Nat.xor c 1 < 24 := by
  have key : ∀ c < 24, Nat.xor c 1 < 24 := by decide
  exact key c h

theorem ev_nil (p : Nat) : ev L [] p = p := rfl

theorem ev_cons (c : Nat) (w : List Nat) (p : Nat) : ev L (c :: w) p = ap L c (ev L w p) := rfl

theorem evI_nil (p : Nat) : evI L [] p = p := rfl

theorem evI_cons (c : Nat) (w : List Nat) (p : Nat) :
    evI L (c :: w) p = evI L w (ap L (Nat.xor c 1) p) := rfl

theorem wv_nil : wv g [] = 1 := by simp [wv]

theorem wv_cons (c : Nat) (w : List Nat) : wv g (c :: w) = g c * wv g w := by simp [wv]

theorem ev_eq (hL : LRep L g) : ∀ (w : List Nat), (∀ c ∈ w, c < 24) →
    ∀ x : Fin 1755, ev L w x = (wv g w x : Nat)
  | [], _, x => by rw [ev_nil, wv_nil, Perm.one_apply]
  | c :: w, hw, x => by
    rw [ev_cons, ev_eq hL w (fun d hd => hw d (List.mem_cons_of_mem c hd)) x,
      hL.1 c (hw c (List.mem_cons_self ..)), wv_cons, Perm.mul_apply]

theorem evI_eq (hL : LRep L g) : ∀ (w : List Nat), (∀ c ∈ w, c < 24) →
    ∀ x : Fin 1755, evI L w x = ((wv g w)⁻¹ x : Nat)
  | [], _, x => by rw [evI_nil, wv_nil, inv_one, Perm.one_apply]
  | c :: w, hw, x => by
    have hc : c < 24 := hw c (List.mem_cons_self ..)
    rw [evI_cons, hL.1 _ (xor_lt hc), evI_eq hL w (fun d hd => hw d (List.mem_cons_of_mem c hd)),
      hL.2 c hc, wv_cons, mul_inv_rev, Perm.mul_apply]

theorem gx_eq (hL : LRep L g) {z : Nat} (hz : z < 24) {t : List Nat} (ht : ∀ c ∈ t, c < 24)
    (y : Fin 1755) : gx L z t y = (xb g z t y : Nat) := by
  have e : gx L z t y = ev L t (ap L z (evI L t (ap L 2 y))) := rfl
  rw [e, hL.1 2 (by decide) y, evI_eq hL t ht, hL.1 z hz, ev_eq hL t ht]
  simp only [xb, Perm.mul_apply]

theorem iter_eq (hL : LRep L g) {z : Nat} (hz : z < 24) {t : List Nat} (ht : ∀ c ∈ t, c < 24) :
    ∀ (m : Nat) (y : Fin 1755), iter L z t m y = ((xb g z t ^ m) y : Nat)
  | 0, y => by rw [pow_zero, Perm.one_apply]; rfl
  | m + 1, y => by
    have e : iter L z t (m + 1) y = gx L z t (iter L z t m y) := rfl
    rw [e, iter_eq hL hz ht m y, gx_eq hL hz ht, pow_succ', Perm.mul_apply]

theorem band_true {a b : Bool} : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem bif_true {c t e : Bool} : bIf(c, t, e) = true ↔ (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

theorem allL_spec {α : Type} {f : α → Bool} : ∀ {l : List α}, allL l f = true → ∀ a ∈ l, f a = true
  | [], _, a, ha => absurd ha (List.not_mem_nil)
  | b :: l, h, a, ha => by
    have e : allL (b :: l) f = bAnd(f b, allL l f) := rfl
    rw [e, band_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h.1
    · exact allL_spec h.2 a ha

theorem walk_spec {z : Nat} : ∀ (E : List (List Nat × Nat)) (q : Nat), walk L z E q = true →
    ∀ (j : Nat) (hj : j < E.length), ev L (E[j]).1 0 = q + j ∧ ((E[j]).2 = 2047 ∨
      ((E[j]).2 < 1755 ∧ iter L z (E[j]).1 13 (E[j]).2 ≠ (E[j]).2))
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | e :: E, q, h, j, hj => by
    have e1 : walk L z (e :: E) q = bAnd(Nat.beq (ev L e.1 0) q,
        bAnd(bIf(Nat.beq e.2 2047, true, bAnd(Nat.blt e.2 1755,
          bIf(Nat.beq (iter L z e.1 13 e.2) e.2, false, true))), walk L z E (Nat.succ q))) := rfl
    rw [e1, band_true, band_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    cases j with
    | zero =>
      refine ⟨by simpa using Nat.eq_of_beq_eq_true h1, ?_⟩
      simp only [List.getElem_cons_zero]
      rcases bif_true.1 h2 with ⟨hc, -⟩ | ⟨hc, hb⟩
      · exact Or.inl (Nat.eq_of_beq_eq_true hc)
      · rw [band_true, bif_true] at hb
        obtain ⟨hlt, hb⟩ := hb
        refine Or.inr ⟨Nat.le_of_ble_eq_true hlt, ?_⟩
        rcases hb with ⟨-, hf⟩ | ⟨hc', -⟩
        · exact absurd hf Bool.false_ne_true
        · exact Nat.ne_of_beq_eq_false hc'
    | succ j =>
      have hj' : j < E.length := by simpa using hj
      obtain ⟨r1, r2⟩ := walk_spec E (Nat.succ q) h3 j hj'
      simp only [List.getElem_cons_succ]
      exact ⟨by rw [r1]; omega, r2⟩

theorem commF_spec {f h : Nat → Nat} (hc : commF f h = true) : ∀ p ∈ bs, f (h p) = h (f p) :=
  fun p hp => Nat.eq_of_beq_eq_true (allL_spec hc p hp)

theorem conjB_spec {a z : Nat} {t : List Nat} (hc : conjB L a t z = true) :
    ∀ p ∈ bs, ap L a p = ev L t (ap L z (evI L t p)) :=
  fun p hp => Nat.eq_of_beq_eq_true (allL_spec hc p hp)

end CFSG.KC.Tits8074

end
