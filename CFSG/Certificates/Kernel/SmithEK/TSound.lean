module

public import Certificates.Data.Kernel.SmithEKT
public import CFSG.Certificates.Kernel.SmithEK.WSound
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
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE
open CFSG.SmithL6.Kernel (ofFn_get!)

theorem fld_xor (k a b : Nat) : fld k (a ^^^ b) = fld k a ^^^ fld k b := by
  unfold fld
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_div_two_pow]
  cases decide (i < 20) <;> simp

theorem fld_zero (k : Nat) : fld k 0 = 0 := by
  simp [fld]

theorem fld_zero_k (X : Nat) : fld 0 X = X % 1048576 := by
  simp [fld]

theorem fld_succ (k X : Nat) : fld (k + 1) X = fld k (X / 1048576) := by
  unfold fld
  rw [Nat.div_div_eq_div_mul, show (1048576 : Nat) = 2 ^ 20 by norm_num, ← Nat.pow_add,
    show 20 + 20 * k = 20 * (k + 1) by ring]

theorem applyL_fld (k : Nat) : ∀ (C : List Nat) (c : Nat),
    fld k (applyL C c) = applyL (C.map (fld k)) c
  | [], _ => fld_zero k
  | x :: C, c => by
    have e : ∀ (l : List Nat) (y c : Nat),
        applyL (y :: l) c = (if c.testBit 0 then y else 0) ^^^ applyL l (c / 2) := fun _ _ _ => rfl
    rw [e, List.map_cons, e, fld_xor, applyL_fld k C]
    split_ifs <;> simp [fld_zero]

theorem packOK_cons (T : List (List (List (List Nat)))) (p : Nat) (P C : List Nat) :
    packOK T (p :: P) C =
      (tvW T p == C.map (· % 1048576) && packOK T P (C.map (· / 1048576))) := rfl

theorem packOK_sound (T : List (List (List (List Nat)))) : ∀ (P C : List Nat),
    packOK T P C = true → ∀ k < P.length, C.map (fld k) = tvW T (P.getD k 0)
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | p :: P, C, h, k, hk => by
    rw [packOK_cons, Bool.and_eq_true, beq_iff_eq] at h
    cases k with
    | zero =>
      rw [List.getD_cons_zero, h.1]
      exact List.map_congr_left fun x _ => fld_zero_k x
    | succ k =>
      rw [List.getD_cons_succ, ← packOK_sound T P _ h.2 k (by simp at hk; omega), List.map_map]
      exact List.map_congr_left fun x _ => fld_succ k x

theorem laneK_cons (B w q : Nat) (P : List Nat) (V : Nat) :
    laneK B w (q :: P) V = ((V % 1048576 == w ||
      (B.testBit (V % 1048576) && B.testBit (V % 1048576 ^^^ w))) && laneK B w P (V / 1048576)) :=
  rfl

theorem laneK_sound (B w : Nat) : ∀ (P : List Nat) (V : Nat), laneK B w P V = true →
    ∀ k < P.length, fld k V = w ∨ (B.testBit (fld k V) = true ∧ B.testBit (fld k V ^^^ w) = true)
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | q :: P, V, h, k, hk => by
    rw [laneK_cons, Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    cases k with
    | zero =>
      rw [fld_zero_k]
      exact h.1
    | succ k =>
      rw [fld_succ]
      exact laneK_sound B w P _ h.2 k (by simp at hk; omega)

theorem chunkT_sound {C W P : List Nat} {a n : Nat} (h : chunkT C W P a n = true) {r : Nat}
    (hr : r < n) (hl : a + r < W.length) :
    laneK (wBits W) (W.getD (a + r) 0) P (applyL C (W.getD (a + r) 0)) = true := by
  unfold chunkT rowsT at h
  rw [List.all_eq_true] at h
  rw [← getD_drop_take W hr]
  exact h _ (getD_mem (by simp; omega))

theorem atLeast_le : ∀ (a b n : Nat), a ≤ b → atLeast b n = true → atLeast a n = true
  | 0, _, _, _, _ => rfl
  | a + 1, 0, _, hab, _ => absurd hab (by omega)
  | a + 1, b + 1, n, hab, h => by
    have e : ∀ c m, atLeast (c + 1) m = (m != 0 && atLeast c (m &&& (m - 1))) := fun _ _ => rfl
    rw [e, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, atLeast_le a b _ (by omega) h.2⟩

theorem tvArr_get {k : Nat} (hk : k < 693) : tvArr[k]! = tvCols k := by
  unfold tvArr
  exact ofFn_get! _ hk

theorem chkT_of (hW : chkW = true)
    (h : ∀ k < 693, ∀ i < 891, applyCols (tvCols k) wtArr[i]! = wtArr[i]! ∨
      ((∃ j < 891, wtArr[j]! = applyCols (tvCols k) wtArr[i]!) ∧
        ∃ l < 891, wtArr[l]! = applyCols (tvCols k) wtArr[i]! ^^^ wtArr[i]!)) :
    chkT = true := by
  unfold chkW at hW
  simp only [Bool.and_eq_true, List.all_eq_true] at hW
  obtain ⟨⟨h1, h2⟩, h3⟩ := hW
  have hidx : ∀ j < 891, wtIdx[wtArr[j]!]! = j := fun j hj => by
    have e := h1 j (List.mem_range.mpr hj)
    rwa [beq_iff_eq] at e
  have hisWt : ∀ l < 891, isWt wtArr[l]! = true := fun l hl => by
    unfold isWt
    rw [hidx l hl]
    simp [hl]
  have hgood : ∀ i < 891, ∀ v, (v = wtArr[i]! ∨ ((∃ j < 891, wtArr[j]! = v) ∧
      ∃ l < 891, wtArr[l]! = v ^^^ wtArr[i]!)) →
      (decide (wtIdx[v]! < 891) && wtArr[wtIdx[v]!]! == v && adjM i wtIdx[v]!) = true := by
    intro i hi v hv
    rcases hv with hv | ⟨⟨j, hj, hj'⟩, l, hl, hle⟩
    · rw [hv, hidx i hi]
      have hm := h2 i (List.mem_range.mpr hi)
      unfold modelOK at hm
      simp only [Bool.and_eq_true] at hm
      have h64 : atLeast 64 (wMask i) = true := hm.1.1.1.2
      unfold adjM
      rw [Nat.and_self, maskArr_get hi]
      simp [hi, atLeast_le 16 64 _ (by omega) h64]
    · rw [← hj'] at hle ⊢
      rw [hidx j hj]
      have e := h3 i (List.mem_range.mpr hi)
      have e2 := e.2 j (List.mem_range.mpr hj)
      have hw : isWt (wtArr[i]! ^^^ wtArr[j]!) = true := by
        rw [Nat.xor_comm, ← hle]
        exact hisWt l hl
      rw [hw, Bool.not_true, Bool.or_false] at e2
      simp [hj, e2]
  unfold chkT
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [tvArr_get hk']
  exact hgood i hi' _ (h k hk' i hi')

end CFSG.SmithE.K
