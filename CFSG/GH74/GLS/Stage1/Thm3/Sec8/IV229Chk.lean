module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229

@[expose] def allLt : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p n && allLt n p

theorem allLt_iff (n : Nat) (p : Nat → Bool) : allLt n p = true ↔ ∀ k, k < n → p k = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

@[expose] def Nt (a : Nat) : Nat := (1684734875308353040 >>> (4 * a)) &&& 15

@[expose] def evN (t0 t1 t2 t3 a : Nat) : Nat :=
  (if a &&& 1 = 0 then 0 else t0) ^^^ (if a &&& 2 = 0 then 0 else t1) ^^^
    (if a &&& 4 = 0 then 0 else t2) ^^^ (if a &&& 8 = 0 then 0 else t3)

theorem evN_lt8 (t0 t1 t2 t3 a : Nat) (ha : a < 8) : evN t0 t1 t2 t3 a = evN t0 t1 t2 0 a := by
  have h : ∀ a < 8, a &&& 8 = 0 := by decide
  simp only [evN, h a ha]
  simp

def ord3B (t0 t1 t2 t3 : Nat) : Bool :=
  allLt 16 fun a => decide (evN t0 t1 t2 t3 (evN t0 t1 t2 t3 (evN t0 t1 t2 t3 a)) = a)

def ord2B (t0 t1 t2 t3 : Nat) : Bool :=
  allLt 16 fun a => decide (evN t0 t1 t2 t3 (evN t0 t1 t2 t3 a) = a)

def nonIdB (t0 t1 t2 t3 : Nat) : Bool :=
  !(allLt 16 fun a => decide (evN t0 t1 t2 t3 a = a))

def goodUpTo (n t0 t1 t2 t3 : Nat) : Bool :=
  allLt n fun a => allLt n fun b =>
    !(decide (Nt a = Nt b)) || decide (Nt (evN t0 t1 t2 t3 a) = Nt (evN t0 t1 t2 t3 b))

def relB (t0 t1 t2 t3 s0 s1 s2 s3 : Nat) : Bool :=
  allLt 16 fun a => decide (evN t0 t1 t2 t3 (evN s0 s1 s2 s3 (evN t0 t1 t2 t3 a)) = evN s0 s1 s2 s3 a)

def forallGood (f : Nat → Nat → Nat → Nat → Bool) : Bool :=
  allLt 16 fun t0 => allLt 16 fun t1 => allLt 16 fun t2 =>
    !(goodUpTo 8 t0 t1 t2 0) || allLt 16 fun t3 => !(goodUpTo 16 t0 t1 t2 t3) || f t0 t1 t2 t3

def checkB : Bool :=
  forallGood fun t0 t1 t2 t3 =>
    !(ord3B t0 t1 t2 t3 && nonIdB t0 t1 t2 t3) ||
      forallGood fun s0 s1 s2 s3 => !(relB t0 t1 t2 t3 s0 s1 s2 s3 && ord2B s0 s1 s2 s3)

theorem checkB_true : checkB = true := by decide +kernel

theorem ord3B_iff (t0 t1 t2 t3 : Nat) : ord3B t0 t1 t2 t3 = true ↔
    ∀ a, a < 16 → evN t0 t1 t2 t3 (evN t0 t1 t2 t3 (evN t0 t1 t2 t3 a)) = a := by
  simp [ord3B, allLt_iff]

theorem ord2B_iff (t0 t1 t2 t3 : Nat) : ord2B t0 t1 t2 t3 = true ↔
    ∀ a, a < 16 → evN t0 t1 t2 t3 (evN t0 t1 t2 t3 a) = a := by
  simp [ord2B, allLt_iff]

theorem nonIdB_iff (t0 t1 t2 t3 : Nat) : nonIdB t0 t1 t2 t3 = true ↔
    ∃ a, a < 16 ∧ evN t0 t1 t2 t3 a ≠ a := by
  rw [nonIdB, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, allLt_iff]
  simp

theorem goodUpTo_iff (n t0 t1 t2 t3 : Nat) : goodUpTo n t0 t1 t2 t3 = true ↔
    ∀ a, a < n → ∀ b, b < n → Nt a = Nt b → Nt (evN t0 t1 t2 t3 a) = Nt (evN t0 t1 t2 t3 b) := by
  simp [goodUpTo, allLt_iff, imp_iff_not_or]

theorem relB_iff (t0 t1 t2 t3 s0 s1 s2 s3 : Nat) : relB t0 t1 t2 t3 s0 s1 s2 s3 = true ↔
    ∀ a, a < 16 → evN t0 t1 t2 t3 (evN s0 s1 s2 s3 (evN t0 t1 t2 t3 a)) = evN s0 s1 s2 s3 a := by
  simp [relB, allLt_iff]

theorem goodUpTo_prefix (t0 t1 t2 t3 : Nat) (h : goodUpTo 16 t0 t1 t2 t3 = true) :
    goodUpTo 8 t0 t1 t2 0 = true := by
  rw [goodUpTo_iff] at h ⊢
  intro a ha b hb hab
  rw [← evN_lt8 t0 t1 t2 t3 a ha, ← evN_lt8 t0 t1 t2 t3 b hb]
  exact h a (by omega) b (by omega) hab

theorem forallGood_sound (f : Nat → Nat → Nat → Nat → Bool) (h : forallGood f = true)
    (t0 t1 t2 t3 : Nat) (h0 : t0 < 16) (h1 : t1 < 16) (h2 : t2 < 16) (h3 : t3 < 16)
    (hg : goodUpTo 16 t0 t1 t2 t3 = true) : f t0 t1 t2 t3 = true := by
  unfold forallGood at h
  simp only [allLt_iff] at h
  have h' := h t0 h0 t1 h1 t2 h2
  rw [goodUpTo_prefix t0 t1 t2 t3 hg] at h'
  simp only [Bool.not_true, Bool.false_or, allLt_iff] at h'
  have h'' := h' t3 h3
  rw [hg] at h''
  simpa using h''

theorem natfin16 (t0 t1 t2 t3 : Nat) (h0 : t0 < 16) (h1 : t1 < 16) (h2 : t2 < 16) (h3 : t3 < 16)
    (hord : ∀ a, a < 16 → evN t0 t1 t2 t3 (evN t0 t1 t2 t3 (evN t0 t1 t2 t3 a)) = a)
    (hnon : ∃ a, a < 16 ∧ evN t0 t1 t2 t3 a ≠ a)
    (hgood : ∀ a, a < 16 → ∀ b, b < 16 → Nt a = Nt b →
      Nt (evN t0 t1 t2 t3 a) = Nt (evN t0 t1 t2 t3 b))
    (s0 s1 s2 s3 : Nat) (g0 : s0 < 16) (g1 : s1 < 16) (g2 : s2 < 16) (g3 : s3 < 16)
    (hord2 : ∀ a, a < 16 → evN s0 s1 s2 s3 (evN s0 s1 s2 s3 a) = a)
    (hgood2 : ∀ a, a < 16 → ∀ b, b < 16 → Nt a = Nt b →
      Nt (evN s0 s1 s2 s3 a) = Nt (evN s0 s1 s2 s3 b))
    (hrel : ∀ a, a < 16 →
      evN t0 t1 t2 t3 (evN s0 s1 s2 s3 (evN t0 t1 t2 t3 a)) = evN s0 s1 s2 s3 a) :
    False := by
  have hA := forallGood_sound _ checkB_true t0 t1 t2 t3 h0 h1 h2 h3
    ((goodUpTo_iff _ _ _ _ _).2 hgood)
  have hB : ord3B t0 t1 t2 t3 = true := (ord3B_iff _ _ _ _).2 hord
  have hC : nonIdB t0 t1 t2 t3 = true := (nonIdB_iff _ _ _ _).2 hnon
  rw [hB, hC] at hA
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at hA
  have hD := forallGood_sound _ hA s0 s1 s2 s3 g0 g1 g2 g3 ((goodUpTo_iff _ _ _ _ _).2 hgood2)
  have hE : relB t0 t1 t2 t3 s0 s1 s2 s3 = true := (relB_iff _ _ _ _ _ _ _ _).2 hrel
  have hF : ord2B s0 s1 s2 s3 = true := (ord2B_iff _ _ _ _).2 hord2
  rw [hE, hF] at hD
  simp at hD

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229
