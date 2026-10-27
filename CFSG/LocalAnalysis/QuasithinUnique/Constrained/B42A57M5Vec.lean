module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.QuasithinUnique.B42A57

abbrev V4 : Type := Fin 4 → ZMod 2

@[expose] def lin (w : Fin 4 → V4) (u : V4) : V4 :=
  fun i => u 0 * w 0 i + u 1 * w 1 i + u 2 * w 2 i + u 3 * w 3 i

@[expose] def wC : Fin 4 → V4 := ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 1, 1, 1]]

@[expose] def wD : Fin 4 → V4 := ![![1, 1, 1, 0], ![1, 1, 0, 0], ![0, 1, 0, 0], ![0, 1, 1, 1]]

@[expose] def wN : Fin 4 → V4 := ![![1, 1, 0, 0], ![1, 0, 0, 0], ![0, 1, 1, 1], ![1, 0, 1, 0]]

@[expose] def Tc (c : V4) (u : V4) : V4 :=
  fun i => c 0 * u i + c 1 * lin wC u i + c 2 * lin wC (lin wC u) i +
    c 3 * lin wC (lin wC (lin wC u)) i

theorem lin_add (w : Fin 4 → V4) (u v : V4) : lin w (u + v) = lin w u + lin w v := by
  funext i
  simp only [lin, Pi.add_apply]
  ring

theorem lin_zero (w : Fin 4 → V4) : lin w 0 = 0 := by
  funext i
  simp [lin]

theorem Tc_add (c u v : V4) : Tc c (u + v) = Tc c u + Tc c v := by
  funext i
  simp only [Tc, lin_add, Pi.add_apply]
  ring

theorem Tc_zero (c : V4) : Tc c 0 = 0 := by
  funext i
  simp [Tc, lin_zero]

theorem Tc_comm : ∀ c u : V4, Tc c (lin wC u) = lin wC (Tc c u) := by
  decide +kernel

@[expose] def code (u : V4) : ℕ := (u 0).val + 2 * (u 1).val + 4 * (u 2).val + 8 * (u 3).val

@[expose] def decodeV (n : ℕ) : V4 :=
  ![((n % 2 : ℕ) : ZMod 2), ((n / 2 % 2 : ℕ) : ZMod 2), ((n / 4 % 2 : ℕ) : ZMod 2),
    ((n / 8 % 2 : ℕ) : ZMod 2)]

theorem code_decode : ∀ n < 16, code (decodeV n) = n := by decide +kernel

theorem decode_code : ∀ u : V4, decodeV (code u) = u := by decide +kernel

theorem code_add : ∀ u v : V4, code (u + v) = code u ^^^ code v := by decide +kernel

theorem code_smul : ∀ (c : ZMod 2) (v : V4), code (fun i => c * v i) = c.val * code v := by
  decide +kernel

theorem code_bit0 : ∀ u : V4, code u &&& 1 = (u 0).val := by decide +kernel

theorem code_bit1 : ∀ u : V4, (code u >>> 1) &&& 1 = (u 1).val := by decide +kernel

theorem code_bit2 : ∀ u : V4, (code u >>> 2) &&& 1 = (u 2).val := by decide +kernel

theorem code_bit3 : ∀ u : V4, (code u >>> 3) &&& 1 = (u 3).val := by decide +kernel

@[expose] def apN (c0 c1 c2 c3 n : ℕ) : ℕ :=
  ((n &&& 1) * c0) ^^^ (((n >>> 1) &&& 1) * c1) ^^^ (((n >>> 2) &&& 1) * c2) ^^^
    (((n >>> 3) &&& 1) * c3)

@[expose] def apC (n : ℕ) : ℕ := apN 2 4 8 15 n

theorem apN_code (w : Fin 4 → V4) (u : V4) :
    apN (code (w 0)) (code (w 1)) (code (w 2)) (code (w 3)) (code u) = code (lin w u) := by
  have e : lin w u = (fun i => u 0 * w 0 i) + (fun i => u 1 * w 1 i) + (fun i => u 2 * w 2 i) +
      (fun i => u 3 * w 3 i) := by
    funext i
    simp [lin]
  rw [e, code_add, code_add, code_add, code_smul, code_smul, code_smul, code_smul]
  unfold apN
  rw [code_bit0, code_bit1, code_bit2, code_bit3]

theorem apC_code (u : V4) : apC (code u) = code (lin wC u) := by
  have := apN_code wC u
  have h0 : code (wC 0) = 2 := by decide +kernel
  have h1 : code (wC 1) = 4 := by decide +kernel
  have h2 : code (wC 2) = 8 := by decide +kernel
  have h3 : code (wC 3) = 15 := by decide +kernel
  rw [h0, h1, h2, h3] at this
  exact this

@[expose] def isSol (a b c d : ℕ) : Bool :=
  let y := apN a b c d
  y (y (y 1)) == 1 &&
    ((List.range 16).all fun n => y (y (y n)) == n && apC (y (apC (y n))) == n)

@[expose] def sols20 : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1, 15, 2, 8), (1, 15, 4, 2), (1, 15, 9, 10), (3, 1, 14, 5), (5, 2, 1, 13), (6, 1, 3, 12),
   (7, 3, 2, 14), (8, 1, 4, 2), (8, 2, 1, 4), (8, 11, 5, 9), (9, 10, 4, 2), (10, 13, 11, 8),
   (11, 5, 12, 4), (12, 9, 10, 7), (13, 6, 2, 3), (14, 1, 7, 4), (15, 2, 1, 8), (15, 7, 13, 11),
   (15, 12, 2, 6), (15, 14, 6, 4)]

@[expose] def check : Bool :=
  (List.range 16).all fun a => (List.range 16).all fun b => (List.range 16).all fun c =>
    (List.range 16).all fun d => !(isSol a b c d) || sols20.contains (a, b, c, d)

set_option maxRecDepth 100000 in
theorem check_eq : check = true := by decide +kernel

theorem mem_sols20 (a b c d : ℕ) (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16)
    (h : isSol a b c d = true) : (a, b, c, d) ∈ sols20 := by
  have h1 := List.all_eq_true.1 check_eq a (List.mem_range.2 ha)
  have h2 := List.all_eq_true.1 h1 b (List.mem_range.2 hb)
  have h3 := List.all_eq_true.1 h2 c (List.mem_range.2 hc)
  have h4 := List.all_eq_true.1 h3 d (List.mem_range.2 hd)
  rw [h] at h4
  simpa using h4

theorem sols20_classified : ∀ e ∈ sols20, ∃ c : V4, (∀ u : V4, Tc c u = 0 → u = 0) ∧
    ((∀ u : V4, Tc c (lin ![decodeV e.1, decodeV e.2.1, decodeV e.2.2.1, decodeV e.2.2.2] u) =
        lin wD (Tc c u)) ∨
      (∀ u : V4, Tc c (lin ![decodeV e.1, decodeV e.2.1, decodeV e.2.2.1, decodeV e.2.2.2] u) =
        lin wN (Tc c u))) := by
  decide +kernel

theorem code_lt (u : V4) : code u < 16 := by
  have := decode_code u
  have h : ∀ v : V4, code v < 16 := by decide +kernel
  exact h u

theorem classify (w : Fin 4 → V4) (h3 : ∀ u, lin w (lin w (lin w u)) = u)
    (h2 : ∀ u, lin wC (lin w (lin wC (lin w u))) = u) :
    ∃ c : V4, (∀ u, Tc c u = 0 → u = 0) ∧
      ((∀ u, Tc c (lin w u) = lin wD (Tc c u)) ∨ (∀ u, Tc c (lin w u) = lin wN (Tc c u))) := by
  have hy : ∀ u, apN (code (w 0)) (code (w 1)) (code (w 2)) (code (w 3)) (code u) =
      code (lin w u) := apN_code w
  have hn : ∀ n < 16, n = code (decodeV n) := fun n hn => (code_decode n hn).symm
  have hsol : isSol (code (w 0)) (code (w 1)) (code (w 2)) (code (w 3)) = true := by
    unfold isSol
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
    refine ⟨?_, fun n hn16 => ⟨?_, ?_⟩⟩
    · have h1 : (1 : ℕ) = code (decodeV 1) := hn 1 (by norm_num)
      rw [h1, hy, hy, hy, h3]
    · rw [hn n hn16, hy, hy, hy, h3]
    · rw [hn n hn16, hy, apC_code, hy, apC_code, h2]
  have hmem := mem_sols20 _ _ _ _ (code_lt _) (code_lt _) (code_lt _) (code_lt _) hsol
  obtain ⟨c, hc1, hc2⟩ := sols20_classified _ hmem
  refine ⟨c, hc1, ?_⟩
  have hw : w = ![decodeV (code (w 0)), decodeV (code (w 1)), decodeV (code (w 2)),
      decodeV (code (w 3))] := by
    funext j
    fin_cases j <;> simp [decode_code]
  simp only at hc2
  rw [← hw] at hc2
  exact hc2

end CFSG.QuasithinUnique.B42A57
