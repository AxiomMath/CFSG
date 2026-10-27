module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoGammaThreeCheck

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwoFive

open QTwoGammaThree

structure V4 where
  x0 : Fin 4
  x1 : Fin 4
  y0 : Fin 4
  y1 : Fin 4
  deriving DecidableEq

@[expose] def frobC (a : Fin 4) : Fin 4 := fMul a a

@[expose] def q4 (v : V4) : Fin 4 := fAdd (fMul v.x0 v.y0) (fMul v.x1 v.y1)

@[expose] def p4 (u v : V4) : Fin 4 :=
  fAdd (fAdd (fMul u.x0 v.y0) (fMul v.x0 u.y0)) (fAdd (fMul u.x1 v.y1) (fMul v.x1 u.y1))

@[expose] def h4 (u v : V4) : Fin 4 :=
  fAdd (fAdd (fMul u.x0 (frobC v.x0)) (fMul u.y0 (frobC v.y0)))
    (fAdd (fMul u.x1 (frobC v.x1)) (fMul u.y1 (frobC v.y1)))

@[expose] def flip4 (v : V4) : V4 := ⟨frobC v.y0, frobC v.y1, frobC v.x0, frobC v.x1⟩

@[expose] def zero4 : V4 := ⟨0, 0, 0, 0⟩

@[expose] def fixed4 (a b : Fin 4) : V4 := ⟨a, b, frobC a, frobC b⟩

@[expose] def allV4 (P : V4 → Bool) : Bool :=
  f4s.all fun a => f4s.all fun b => f4s.all fun c => f4s.all fun d => P ⟨a, b, c, d⟩

@[expose] def blockOK (g : V4) : Bool :=
  !(q4 g == 0 && h4 g g != 0) || (g.x1 == 0 && g.y1 == 0) || (g.x0 == 0 && g.y0 == 0)

@[expose] def blockCheck : Bool := allV4 blockOK

@[expose] def rowOK (v : V4) : Bool := (q4 v == 0 && h4 v v == 0) || (q4 v != 0 && h4 v v == 1)

@[expose] def alt1 (v : V4) : Bool := allV4 fun x => !(p4 x v == 0 && h4 x v == 0) || q4 x == 0

@[expose] def pairOK (v u w : V4) : Bool :=
  flip4 u == u && flip4 w == w && q4 u == 0 && q4 w == 0 && p4 u w == 1 && p4 u v == 0 &&
    h4 u v == 0 && p4 w v == 0 && h4 w v == 0 &&
    allV4 fun x => !(p4 x v == 0 && h4 x v == 0 && p4 x u == 0 && p4 x w == 0) || q4 x == 0

@[expose] def alt2 (v : V4) : Bool :=
  f4s.any fun a => f4s.any fun b => f4s.any fun c => f4s.any fun d =>
    pairOK v (fixed4 a b) (fixed4 c d)

@[expose] def hypCheck : Bool := allV4 fun v => v == zero4 || !rowOK v || alt1 v || alt2 v

@[expose] def twC (v : V6) : V6 :=
  ⟨frobC v.x0, frobC v.y1, frobC v.y2, frobC v.y0, frobC v.x1, frobC v.x2⟩

@[expose] def zOK (x z : V6) : Bool :=
  pC x z == 0 && pC x (twC z) == 0 && qC z == 0 && pC z (twC z) != 0

@[expose] def twOK (x : V6) : Bool :=
  !(qC x == 0 && pC x (twC x) != 0) ||
    (f4s.any fun a => f4s.any fun b => f4s.any fun c => f4s.any fun d =>
      zOK x ⟨a, b, 0, c, d, 0⟩) ||
    (f4s.any fun a => f4s.any fun b => f4s.any fun c => f4s.any fun d =>
      zOK x ⟨a, 0, b, c, 0, d⟩)

@[expose] def twCheck : Bool :=
  f4s.all fun a0 => f4s.all fun a1 => f4s.all fun a2 => f4s.all fun b0 => f4s.all fun b1 =>
    f4s.all fun b2 => twOK ⟨a0, a1, a2, b0, b1, b2⟩

theorem blockCheck_eq_true : blockCheck = true := by decide +kernel

theorem hypCheck_eq_true : hypCheck = true := by decide +kernel

theorem twCheck_eq_true : twCheck = true := by decide +kernel

private theorem q5_mem_f4s : ∀ a : Fin 4, a ∈ f4s
  | ⟨0, _⟩ => by decide +revert
  | ⟨1, _⟩ => by decide +revert
  | ⟨2, _⟩ => by decide +revert
  | ⟨3, _⟩ => by decide +revert
  | ⟨n + 4, h⟩ => absurd h (by omega)

theorem allV4_spec {P : V4 → Bool} (h : allV4 P = true) (v : V4) : P v = true := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [allV4, List.all_eq_true] at h
  exact h a (q5_mem_f4s a) b (q5_mem_f4s b) c (q5_mem_f4s c) d (q5_mem_f4s d)

theorem block_spec (g : V4) (hq : q4 g = 0) (hh : h4 g g ≠ 0) :
    (g.x1 = 0 ∧ g.y1 = 0) ∨ (g.x0 = 0 ∧ g.y0 = 0) := by
  have h := allV4_spec blockCheck_eq_true g
  simpa [blockOK, hq, hh] using h

theorem hyp_spec (v : V4) (hv : v ≠ zero4)
    (hrow : (q4 v = 0 ∧ h4 v v = 0) ∨ (q4 v ≠ 0 ∧ h4 v v = 1)) :
    (∀ x, p4 x v = 0 → h4 x v = 0 → q4 x = 0) ∨
    ∃ u w, flip4 u = u ∧ flip4 w = w ∧ q4 u = 0 ∧ q4 w = 0 ∧ p4 u w = 1 ∧ p4 u v = 0 ∧
      h4 u v = 0 ∧ p4 w v = 0 ∧ h4 w v = 0 ∧
      ∀ x, p4 x v = 0 → h4 x v = 0 → p4 x u = 0 → p4 x w = 0 → q4 x = 0 := by
  have h := allV4_spec hypCheck_eq_true v
  have hrow' : rowOK v = true := by
    rcases hrow with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [rowOK, h1, h2]
  simp only [hrow', Bool.not_true, Bool.or_false, Bool.or_eq_true, beq_iff_eq, hv,
    false_or] at h
  rcases h with h | h
  · left
    intro x hx hx'
    simpa [hx, hx'] using allV4_spec h x
  · right
    simp only [alt2, List.any_eq_true] at h
    obtain ⟨a, -, b, -, c, -, d, -, h⟩ := h
    simp only [pairOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
    refine ⟨_, _, h1, h2, h3, h4, h5, h6, h7, h8, h9, fun x hx hx' hxu hxw => ?_⟩
    simpa [hx, hx', hxu, hxw] using allV4_spec h10 x

theorem tw_spec (x : V6) (hq : qC x = 0) (hp : pC x (twC x) ≠ 0) :
    ∃ z : V6, qC z = 0 ∧ pC z (twC z) ≠ 0 ∧ pC x z = 0 ∧ pC x (twC z) = 0 ∧
      ((z.x2 = 0 ∧ z.y2 = 0) ∨ (z.x1 = 0 ∧ z.y1 = 0)) := by
  have h : twOK x = true := by
    have hc := twCheck_eq_true
    obtain ⟨a0, a1, a2, b0, b1, b2⟩ := x
    simp only [twCheck, List.all_eq_true] at hc
    exact hc a0 (q5_mem_f4s a0) a1 (q5_mem_f4s a1) a2 (q5_mem_f4s a2) b0 (q5_mem_f4s b0) b1
      (q5_mem_f4s b1) b2 (q5_mem_f4s b2)
  have hx : (qC x == 0 && pC x (twC x) != 0) = true := by simp [hq, hp]
  rw [twOK, hx] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨a, -, b, -, c, -, d, -, h⟩ | ⟨a, -, b, -, c, -, d, -, h⟩
  · simp only [zOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    exact ⟨_, h.1.2, h.2, h.1.1.1, h.1.1.2, Or.inl ⟨rfl, rfl⟩⟩
  · simp only [zOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    exact ⟨_, h.1.2, h.2, h.1.1.1, h.1.1.2, Or.inr ⟨rfl, rfl⟩⟩

end CFSG.ClassicalInvolution.PhanDn.QTwoFive
