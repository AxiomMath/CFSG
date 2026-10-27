module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Hom.Defs

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

@[ext] structure T7 (L : Type) where
  s : L
  a1 : L
  a2 : L
  a3 : L
  b12 : L
  b13 : L
  b23 : L

namespace T7

variable {L : Type} [Field L]

@[expose] instance : Add (T7 L) := ⟨fun x y => ⟨x.s + y.s, x.a1 + y.a1, x.a2 + y.a2, x.a3 + y.a3,
  x.b12 + y.b12, x.b13 + y.b13, x.b23 + y.b23⟩⟩

@[expose] instance : Zero (T7 L) := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩

@[expose] instance : SMul L (T7 L) := ⟨fun c x => ⟨c * x.s, c * x.a1, c * x.a2, c * x.a3, c * x.b12,
  c * x.b13, c * x.b23⟩⟩

@[simp] theorem add_s (x y : T7 L) : (x + y).s = x.s + y.s := rfl
@[simp] theorem add_a1 (x y : T7 L) : (x + y).a1 = x.a1 + y.a1 := rfl
@[simp] theorem add_a2 (x y : T7 L) : (x + y).a2 = x.a2 + y.a2 := rfl
@[simp] theorem add_a3 (x y : T7 L) : (x + y).a3 = x.a3 + y.a3 := rfl
@[simp] theorem add_b12 (x y : T7 L) : (x + y).b12 = x.b12 + y.b12 := rfl
@[simp] theorem add_b13 (x y : T7 L) : (x + y).b13 = x.b13 + y.b13 := rfl
@[simp] theorem add_b23 (x y : T7 L) : (x + y).b23 = x.b23 + y.b23 := rfl
@[simp] theorem zero_s : (0 : T7 L).s = 0 := rfl
@[simp] theorem zero_a1 : (0 : T7 L).a1 = 0 := rfl
@[simp] theorem zero_a2 : (0 : T7 L).a2 = 0 := rfl
@[simp] theorem zero_a3 : (0 : T7 L).a3 = 0 := rfl
@[simp] theorem zero_b12 : (0 : T7 L).b12 = 0 := rfl
@[simp] theorem zero_b13 : (0 : T7 L).b13 = 0 := rfl
@[simp] theorem zero_b23 : (0 : T7 L).b23 = 0 := rfl
@[simp] theorem smul_s (c : L) (x : T7 L) : (c • x).s = c * x.s := rfl
@[simp] theorem smul_a1 (c : L) (x : T7 L) : (c • x).a1 = c * x.a1 := rfl
@[simp] theorem smul_a2 (c : L) (x : T7 L) : (c • x).a2 = c * x.a2 := rfl
@[simp] theorem smul_a3 (c : L) (x : T7 L) : (c • x).a3 = c * x.a3 := rfl
@[simp] theorem smul_b12 (c : L) (x : T7 L) : (c • x).b12 = c * x.b12 := rfl
@[simp] theorem smul_b13 (c : L) (x : T7 L) : (c • x).b13 = c * x.b13 := rfl
@[simp] theorem smul_b23 (c : L) (x : T7 L) : (c • x).b23 = c * x.b23 := rfl

@[expose] def opG5 (c : L) (x : T7 L) : T7 L :=
  { x with a3 := x.a3 + c ^ 2 * x.a1, b13 := x.b13 + c * x.a1, b23 := x.b23 + c * x.b12 }

@[expose] def opG5n (c : L) (x : T7 L) : T7 L :=
  { x with a1 := x.a1 + c ^ 2 * x.a3, b13 := x.b13 + c * x.a3, b12 := x.b12 + c * x.b23 }

@[expose] def opA3 (c : L) (x : T7 L) : T7 L :=
  { x with b12 := x.b12 + c * x.a1, a2 := x.a2 + c ^ 2 * x.a1, b23 := x.b23 + c * x.b13 }

@[expose] def opA4 (c : L) (x : T7 L) : T7 L :=
  { x with b13 := x.b13 + c * x.b12, b23 := x.b23 + c * x.a2, a3 := x.a3 + c ^ 2 * x.a2 }

@[simp] theorem opG5_s (c : L) (x : T7 L) : (opG5 c x).s = x.s := rfl
@[simp] theorem opG5_a1 (c : L) (x : T7 L) : (opG5 c x).a1 = x.a1 := rfl
@[simp] theorem opG5_a2 (c : L) (x : T7 L) : (opG5 c x).a2 = x.a2 := rfl
@[simp] theorem opG5_a3 (c : L) (x : T7 L) : (opG5 c x).a3 = x.a3 + c ^ 2 * x.a1 := rfl
@[simp] theorem opG5_b12 (c : L) (x : T7 L) : (opG5 c x).b12 = x.b12 := rfl
@[simp] theorem opG5_b13 (c : L) (x : T7 L) : (opG5 c x).b13 = x.b13 + c * x.a1 := rfl
@[simp] theorem opG5_b23 (c : L) (x : T7 L) : (opG5 c x).b23 = x.b23 + c * x.b12 := rfl
@[simp] theorem opG5n_s (c : L) (x : T7 L) : (opG5n c x).s = x.s := rfl
@[simp] theorem opG5n_a1 (c : L) (x : T7 L) : (opG5n c x).a1 = x.a1 + c ^ 2 * x.a3 := rfl
@[simp] theorem opG5n_a2 (c : L) (x : T7 L) : (opG5n c x).a2 = x.a2 := rfl
@[simp] theorem opG5n_a3 (c : L) (x : T7 L) : (opG5n c x).a3 = x.a3 := rfl
@[simp] theorem opG5n_b12 (c : L) (x : T7 L) : (opG5n c x).b12 = x.b12 + c * x.b23 := rfl
@[simp] theorem opG5n_b13 (c : L) (x : T7 L) : (opG5n c x).b13 = x.b13 + c * x.a3 := rfl
@[simp] theorem opG5n_b23 (c : L) (x : T7 L) : (opG5n c x).b23 = x.b23 := rfl
@[simp] theorem opA3_s (c : L) (x : T7 L) : (opA3 c x).s = x.s := rfl
@[simp] theorem opA3_a1 (c : L) (x : T7 L) : (opA3 c x).a1 = x.a1 := rfl
@[simp] theorem opA3_a2 (c : L) (x : T7 L) : (opA3 c x).a2 = x.a2 + c ^ 2 * x.a1 := rfl
@[simp] theorem opA3_a3 (c : L) (x : T7 L) : (opA3 c x).a3 = x.a3 := rfl
@[simp] theorem opA3_b12 (c : L) (x : T7 L) : (opA3 c x).b12 = x.b12 + c * x.a1 := rfl
@[simp] theorem opA3_b13 (c : L) (x : T7 L) : (opA3 c x).b13 = x.b13 := rfl
@[simp] theorem opA3_b23 (c : L) (x : T7 L) : (opA3 c x).b23 = x.b23 + c * x.b13 := rfl
@[simp] theorem opA4_s (c : L) (x : T7 L) : (opA4 c x).s = x.s := rfl
@[simp] theorem opA4_a1 (c : L) (x : T7 L) : (opA4 c x).a1 = x.a1 := rfl
@[simp] theorem opA4_a2 (c : L) (x : T7 L) : (opA4 c x).a2 = x.a2 := rfl
@[simp] theorem opA4_a3 (c : L) (x : T7 L) : (opA4 c x).a3 = x.a3 + c ^ 2 * x.a2 := rfl
@[simp] theorem opA4_b12 (c : L) (x : T7 L) : (opA4 c x).b12 = x.b12 := rfl
@[simp] theorem opA4_b13 (c : L) (x : T7 L) : (opA4 c x).b13 = x.b13 + c * x.b12 := rfl
@[simp] theorem opA4_b23 (c : L) (x : T7 L) : (opA4 c x).b23 = x.b23 + c * x.a2 := rfl

@[expose] def opU (r s c : L) (x : T7 L) : T7 L := opA3 s (opA4 r (opG5 c x))

end T7

structure PCl {L : Type} [Field L] (Fr : L →+* L) (P : Set (T7 L)) : Prop where
  zero : (0 : T7 L) ∈ P
  add : ∀ x y, x ∈ P → y ∈ P → x + y ∈ P
  smul : ∀ ζ : L, Fr ζ = ζ → ∀ x ∈ P, ζ • x ∈ P
  g5 : ∀ c : L, Fr c = c → ∀ x ∈ P, T7.opG5 c x ∈ P
  g5n : ∀ c : L, Fr c = c → ∀ x ∈ P, T7.opG5n c x ∈ P
  u : ∀ s c : L, Fr (Fr s) = s → c + Fr c = s * Fr s → ∀ x ∈ P, T7.opU (Fr s) s c x ∈ P

section Alg

open T7

macro "char2" : tactic =>
  `(tactic| first | (ring_nf; done) | (ring_nf; simp [CharTwo.two_eq_zero]; done))

variable {L : Type} [Field L] [CharP L 2] {Fr : L →+* L} {P : Set (T7 L)}

theorem two_eq : (2 : L) = 0 := CharTwo.two_eq_zero

@[expose] def InE (Fr : L →+* L) (l : L) : Prop := Fr (Fr l) = l

theorem InE.add {l m : L} (hl : InE Fr l) (hm : InE Fr m) : InE Fr (l + m) := by
  unfold InE at *; rw [map_add, map_add, hl, hm]

theorem InE.mul {l m : L} (hl : InE Fr l) (hm : InE Fr m) : InE Fr (l * m) := by
  unfold InE at *; rw [map_mul, map_mul, hl, hm]

theorem InE.pow {l : L} (hl : InE Fr l) (n : ℕ) : InE Fr (l ^ n) := by
  unfold InE at *; rw [map_pow, map_pow, hl]

theorem InE.one : InE Fr (1 : L) := by unfold InE; rw [map_one, map_one]

theorem InE.zero : InE Fr (0 : L) := by unfold InE; rw [map_zero, map_zero]

theorem InE.of_fixed {l : L} (h : Fr l = l) : InE Fr l := by unfold InE; rw [h, h]

theorem InE.inv {l : L} (hl : InE Fr l) : InE Fr l⁻¹ := by
  unfold InE at *; rw [map_inv₀, map_inv₀, hl]

theorem InE.div {l m : L} (hl : InE Fr l) (hm : InE Fr m) : InE Fr (l / m) := by
  rw [div_eq_mul_inv]; exact hl.mul hm.inv

theorem InE.of_sum {c : L} (h : c + Fr c = 1) : InE Fr c := by
  unfold InE
  have h2 : Fr c + Fr (Fr c) = 1 := by
    have := congrArg Fr h
    rwa [map_add, map_one] at this
  linear_combination h2 - h

theorem D5 (hP : PCl Fr P) {x : T7 L} (hx : x ∈ P) {c : L} (hc : Fr c = c) :
    opG5 c x + x ∈ P := hP.add _ _ (hP.g5 c hc x hx) hx

theorem D5n (hP : PCl Fr P) {x : T7 L} (hx : x ∈ P) {c : L} (hc : Fr c = c) :
    opG5n c x + x ∈ P := hP.add _ _ (hP.g5n c hc x hx) hx

theorem DU (hP : PCl Fr P) {x : T7 L} (hx : x ∈ P) {c : L} (hc : c + Fr c = 1) :
    opU 1 1 c x + x ∈ P := by
  have h := hP.u 1 c (by rw [map_one, map_one]) (by rw [map_one, one_mul]; exact hc) x hx
  rw [map_one] at h
  exact hP.add _ _ h hx

theorem trick5 (hP : PCl Fr P) {x : T7 L} (hx : x ∈ P) {ζ : L} (hζ : Fr ζ = ζ) :
    (⟨0, 0, 0, 0, 0, (ζ + ζ ^ 2) * x.a1, (ζ + ζ ^ 2) * x.b12⟩ : T7 L) ∈ P := by
  have h1 := D5 hP hx hζ
  have h2 := hP.smul (ζ ^ 2) (by rw [map_pow, hζ]) _ (D5 hP hx (c := 1) (map_one Fr))
  have := hP.add _ _ h1 h2
  convert this using 1
  ext <;> simp <;> char2

theorem trick5n (hP : PCl Fr P) {x : T7 L} (hx : x ∈ P) {ζ : L} (hζ : Fr ζ = ζ) :
    (⟨0, 0, 0, 0, (ζ + ζ ^ 2) * x.b23, (ζ + ζ ^ 2) * x.a3, 0⟩ : T7 L) ∈ P := by
  have h1 := D5n hP hx hζ
  have h2 := hP.smul (ζ ^ 2) (by rw [map_pow, hζ]) _ (D5n hP hx (c := 1) (map_one Fr))
  have := hP.add _ _ h1 h2
  convert this using 1
  ext <;> simp <;> char2

theorem ne_of_ne {ζ a : L} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (ha : a ≠ 0) : (ζ + ζ ^ 2) * a ≠ 0 := by
  refine mul_ne_zero ?_ ha
  have : ζ + ζ ^ 2 = ζ * (1 + ζ) := by ring
  rw [this]
  refine mul_ne_zero hζ0 fun h => hζ1 ?_
  linear_combination h - (CharTwo.two_eq_zero (R := L))

theorem soc_of_ne (hP : PCl Fr P) {ζ : L} (hζ : Fr ζ = ζ) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    {c : L} (hc : c + Fr c = 1) {x : T7 L} (hx : x ∈ P)
    (hne : x.a1 ≠ 0 ∨ x.a2 ≠ 0 ∨ x.a3 ≠ 0 ∨ x.b12 ≠ 0 ∨ x.b13 ≠ 0 ∨ x.b23 ≠ 0) :
    ∃ z ∈ P, z.s = 0 ∧ z.a1 = 0 ∧ z.a2 = 0 ∧ z.a3 = 0 ∧ (z.b12 ≠ 0 ∨ z.b13 ≠ 0 ∨ z.b23 ≠ 0) := by
  by_cases hA : x.a1 ≠ 0 ∨ x.b12 ≠ 0
  · refine ⟨_, trick5 hP hx hζ, rfl, rfl, rfl, rfl, ?_⟩
    rcases hA with h | h
    · exact Or.inr (Or.inl (ne_of_ne hζ0 hζ1 h))
    · exact Or.inr (Or.inr (ne_of_ne hζ0 hζ1 h))
  push Not at hA
  obtain ⟨ha1, hb12⟩ := hA
  by_cases hB : x.a3 ≠ 0 ∨ x.b23 ≠ 0
  · refine ⟨_, trick5n hP hx hζ, rfl, rfl, rfl, rfl, ?_⟩
    rcases hB with h | h
    · exact Or.inr (Or.inl (ne_of_ne hζ0 hζ1 h))
    · exact Or.inl (ne_of_ne hζ0 hζ1 h)
  push Not at hB
  obtain ⟨ha3, hb23⟩ := hB
  have hU := DU hP hx hc
  by_cases hC : x.a2 ≠ 0
  ·
    have hy3 : (opU 1 1 c x + x).a3 = x.a2 := by
      simp [opU, ha1] <;> char2
    refine ⟨_, trick5n hP hU hζ, rfl, rfl, rfl, rfl, Or.inr (Or.inl ?_)⟩
    simp only [hy3]
    exact ne_of_ne hζ0 hζ1 hC
  · push Not at hC
    have hb13 : x.b13 ≠ 0 := by
      rcases hne with h | h | h | h | h | h
      · exact absurd ha1 h
      · exact absurd hC h
      · exact absurd ha3 h
      · exact absurd hb12 h
      · exact h
      · exact absurd hb23 h
    have e1 : (opU 1 1 c x + x).s = 0 := by simp [opU] <;> char2
    have e2 : (opU 1 1 c x + x).a1 = 0 := by simp [opU, ha1] <;> char2
    have e3 : (opU 1 1 c x + x).a2 = 0 := by simp [opU, ha1] <;> char2
    have e4 : (opU 1 1 c x + x).a3 = 0 := by simp [opU, ha1, hC] <;> char2
    have e5 : (opU 1 1 c x + x).b23 = x.b13 := by simp [opU, ha1, hC, hb12] <;> char2
    refine ⟨opU 1 1 c x + x, hU, e1, e2, e3, e4, Or.inr (Or.inr ?_)⟩
    rw [e5]
    exact hb13

theorem b23_of_soc (hP : PCl Fr P) {c : L} (hc : c + Fr c = 1) {z : T7 L} (hz : z ∈ P)
    (hs : z.s = 0) (ha1 : z.a1 = 0) (ha2 : z.a2 = 0) (ha3 : z.a3 = 0)
    (hne : z.b12 ≠ 0 ∨ z.b13 ≠ 0 ∨ z.b23 ≠ 0) :
    ∃ l : L, l ≠ 0 ∧ (⟨0, 0, 0, 0, 0, 0, l⟩ : T7 L) ∈ P := by
  by_cases h12 : z.b12 ≠ 0
  · refine ⟨z.b12, h12, ?_⟩
    have h := D5 hP hz (c := 1) (map_one Fr)
    convert h using 1
    ext <;> simp [hs, ha1, ha3] <;> char2
  push Not at h12
  by_cases h13 : z.b13 ≠ 0
  · refine ⟨z.b13, h13, ?_⟩
    have h := DU hP hz hc
    convert h using 1
    ext <;> simp [opU, hs, ha1, ha2, ha3, h12] <;> char2
  push Not at h13
  have h23 : z.b23 ≠ 0 := by
    rcases hne with h | h | h
    · exact absurd h12 h
    · exact absurd h13 h
    · exact h
  refine ⟨z.b23, h23, ?_⟩
  convert hz using 1
  ext <;> simp [hs, ha1, ha2, ha3, h12, h13]

theorem all_of_A3 (hP : PCl Fr P) {ζ : L} (hζ : Fr ζ = ζ) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    {c : L} (hc : c + Fr c = 1)
    (hS : ∀ l, InE Fr l → (⟨l, 0, 0, 0, 0, 0, 0⟩ : T7 L) ∈ P)
    (hA3 : ∀ l, InE Fr l → (⟨0, 0, 0, l, 0, 0, 0⟩ : T7 L) ∈ P) :
    ∀ x : T7 L, InE Fr x.s → InE Fr x.a1 → InE Fr x.a2 → InE Fr x.a3 → InE Fr x.b12 →
      InE Fr x.b13 → InE Fr x.b23 → x ∈ P := by
  have hd : ζ + ζ ^ 2 ≠ 0 := by
    have := ne_of_ne (a := (1 : L)) hζ0 hζ1 one_ne_zero
    simpa using this
  have hdE : InE Fr (ζ + ζ ^ 2) := InE.of_fixed (by rw [map_add, map_pow, hζ])
  have hcE : InE Fr c := InE.of_sum hc
  have hB13 : ∀ m, InE Fr m → (⟨0, 0, 0, 0, 0, m, 0⟩ : T7 L) ∈ P := by
    intro m hm
    have h := trick5n hP (hA3 (m / (ζ + ζ ^ 2)) (hm.div hdE)) hζ
    have e : (ζ + ζ ^ 2) * (m / (ζ + ζ ^ 2)) = m := by
      rw [mul_div_assoc']; exact mul_div_cancel_left₀ m hd
    convert h using 1
    ext <;> simp only [mul_zero, e]
  have hA1 : ∀ l, InE Fr l → (⟨0, l, 0, 0, 0, 0, 0⟩ : T7 L) ∈ P := by
    intro l hl
    have h := hP.add _ _ (D5n hP (hA3 l hl) (c := 1) (map_one Fr)) (hB13 l hl)
    convert h using 1
    ext <;> simp <;> char2
  have hB23 : ∀ m, InE Fr m → (⟨0, 0, 0, 0, 0, 0, m⟩ : T7 L) ∈ P := by
    intro m hm
    have h := DU hP (hB13 m hm) hc
    convert h using 1
    ext <;> simp [opU] <;> char2
  have hB12 : ∀ m, InE Fr m → (⟨0, 0, 0, 0, m, 0, 0⟩ : T7 L) ∈ P := by
    intro m hm
    have h := D5n hP (hB23 m hm) (c := 1) (map_one Fr)
    convert h using 1
    ext <;> simp <;> char2
  have hA2 : ∀ l, InE Fr l → (⟨0, 0, l, 0, 0, 0, 0⟩ : T7 L) ∈ P := by
    intro l hl
    have h0 := DU hP (hA1 l hl) hc
    have h1 := hP.add _ _ h0 (hA3 (c ^ 2 * l) ((hcE.pow 2).mul hl))
    have h2 := hP.add _ _ h1 (hB12 l hl)
    have h3 := hP.add _ _ h2 (hB13 (c * l) (hcE.mul hl))
    have h4 := hP.add _ _ h3 (hB23 (c * l) (hcE.mul hl))
    convert h4 using 1
    ext <;> simp [opU] <;> char2
  intro x h0 h1 h2 h3 h4 h5 h6
  have e : x = ⟨x.s, 0, 0, 0, 0, 0, 0⟩ + (⟨0, x.a1, 0, 0, 0, 0, 0⟩ + (⟨0, 0, x.a2, 0, 0, 0, 0⟩ +
      (⟨0, 0, 0, x.a3, 0, 0, 0⟩ + (⟨0, 0, 0, 0, x.b12, 0, 0⟩ + (⟨0, 0, 0, 0, 0, x.b13, 0⟩ +
        ⟨0, 0, 0, 0, 0, 0, x.b23⟩))))) := by
    ext <;> simp
  rw [e]
  exact hP.add _ _ (hS _ h0) (hP.add _ _ (hA1 _ h1) (hP.add _ _ (hA2 _ h2)
    (hP.add _ _ (hA3 _ h3) (hP.add _ _ (hB12 _ h4) (hP.add _ _ (hB13 _ h5) (hB23 _ h6))))))

end Alg


end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even
