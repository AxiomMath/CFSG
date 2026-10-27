module

public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LyonsUnitaryFour

structure LyonsMoments where
  m0 : ℕ
  m1 : ℕ
  m2 : ℕ
  m3 : ℕ
  m4 : ℕ
  m5 : ℕ
  m6 : ℕ
  m7 : ℕ
  deriving DecidableEq

namespace LyonsMoments

@[expose] def get (x : LyonsMoments) : Fin 8 → ℕ :=
  ![x.m0, x.m1, x.m2, x.m3, x.m4, x.m5, x.m6, x.m7]

theorem ext_get {x y : LyonsMoments} (h : ∀ j, x.get j = y.get j) : x = y := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := x
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ := y
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  simp only [get, Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7
  subst h0 h1 h2 h3 h4 h5 h6 h7
  rfl

@[expose] def zero : LyonsMoments := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

@[expose] def add (x y : LyonsMoments) : LyonsMoments :=
  ⟨x.m0 + y.m0, x.m1 + y.m1, x.m2 + y.m2, x.m3 + y.m3, x.m4 + y.m4, x.m5 + y.m5, x.m6 + y.m6,
    x.m7 + y.m7⟩

@[expose] def smul (x : LyonsMoments) (k : ℕ) : LyonsMoments :=
  ⟨k * x.m0, k * x.m1, k * x.m2, k * x.m3, k * x.m4, k * x.m5, k * x.m6, k * x.m7⟩

@[expose] def sub (x y : LyonsMoments) : LyonsMoments :=
  ⟨x.m0 - y.m0, x.m1 - y.m1, x.m2 - y.m2, x.m3 - y.m3, x.m4 - y.m4, x.m5 - y.m5, x.m6 - y.m6,
    x.m7 - y.m7⟩

@[expose] def total (x : LyonsMoments) : ℕ :=
  x.m0 + x.m1 + x.m2 + x.m3 + x.m4 + x.m5 + x.m6 + x.m7

@[expose] def supportStep (x s : ℕ) : Bool := x == 0 || s != 0

@[expose] def supported (x s : LyonsMoments) : Bool :=
  supportStep x.m0 s.m0 && supportStep x.m1 s.m1 && supportStep x.m2 s.m2 &&
    supportStep x.m3 s.m3 && supportStep x.m4 s.m4 && supportStep x.m5 s.m5 &&
    supportStep x.m6 s.m6 && supportStep x.m7 s.m7

@[expose] def boundStep (w t acc : ℕ) : ℕ := if w = 0 then acc else min acc (t / w)

@[expose] def bound (w T : LyonsMoments) : ℕ :=
  boundStep w.m0 T.m0 <| boundStep w.m1 T.m1 <| boundStep w.m2 T.m2 <| boundStep w.m3 T.m3 <|
    boundStep w.m4 T.m4 <| boundStep w.m5 T.m5 <| boundStep w.m6 T.m6 <|
      boundStep w.m7 T.m7 T.total

@[simp] theorem get_zero (j : Fin 8) : zero.get j = 0 := by
  fin_cases j <;> rfl

@[simp] theorem get_add (x y : LyonsMoments) (j : Fin 8) :
    (x.add y).get j = x.get j + y.get j := by
  fin_cases j <;> rfl

@[simp] theorem get_smul (x : LyonsMoments) (k : ℕ) (j : Fin 8) :
    (x.smul k).get j = k * x.get j := by
  fin_cases j <;> rfl

@[simp] theorem get_sub (x y : LyonsMoments) (j : Fin 8) :
    (x.sub y).get j = x.get j - y.get j := by
  fin_cases j <;> rfl

theorem supported_eq_true {x s : LyonsMoments} (h : ∀ j, x.get j ≠ 0 → s.get j ≠ 0) :
    x.supported s = true := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := x
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7⟩ := s
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  simp only [get, Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [supported, supportStep, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq]
  omega

theorem le_boundStep {k w t acc : ℕ} (hacc : k ≤ acc) (h : k * w ≤ t) :
    k ≤ boundStep w t acc := by
  unfold boundStep
  split_ifs with hw
  · exact hacc
  · exact le_min hacc ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hw)).mpr h)

theorem le_bound {w T : LyonsMoments} {k : ℕ} (hw : w ≠ zero) (h : ∀ j, k * w.get j ≤ T.get j) :
    k ≤ bound w T := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := w
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩ := T
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  simp only [get, Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7
  have htot : k ≤ t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 := by
    by_contra hk
    apply hw
    simp only [zero, mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      by_contra hne <;> nlinarith [Nat.one_le_iff_ne_zero.mpr hne]
  simp only [bound, total]
  exact le_boundStep (le_boundStep (le_boundStep (le_boundStep (le_boundStep (le_boundStep
    (le_boundStep (le_boundStep htot h7) h6) h5) h4) h3) h2) h1) h0

end LyonsMoments

open LyonsMoments

@[expose] def lyonsMomentSum (ws : List LyonsMoments) : LyonsMoments :=
  ws.foldr LyonsMoments.add LyonsMoments.zero

@[expose] def lyonsCombination : List ℕ → List LyonsMoments → LyonsMoments
  | k :: ks, w :: ws => (w.smul k).add (lyonsCombination ks ws)
  | _, _ => LyonsMoments.zero

@[expose] def lyonsLevels : List LyonsMoments → List (LyonsMoments × LyonsMoments)
  | [] => []
  | w :: ws => (w, w.add (lyonsMomentSum ws)) :: lyonsLevels ws

@[expose] def lyonsSearch :
    List (LyonsMoments × LyonsMoments) → LyonsMoments → List (List ℕ)
  | [], T => if T = LyonsMoments.zero then [[]] else []
  | (w, s) :: rest, T =>
    if T.supported s then
      (List.range (bound w T + 1)).flatMap fun k =>
        (lyonsSearch rest (T.sub (w.smul k))).map (k :: ·)
    else []

theorem lyonsMomentSum_get_ne_zero {ws : List LyonsMoments} {j : Fin 8} {w : LyonsMoments}
    (hw : w ∈ ws) (hj : w.get j ≠ 0) : (lyonsMomentSum ws).get j ≠ 0 := by
  induction ws with
  | nil => simp at hw
  | cons v ws ih =>
    simp only [lyonsMomentSum, List.foldr_cons, get_add] at ih ⊢
    rcases List.mem_cons.mp hw with rfl | hw
    · omega
    · have := ih hw
      omega

theorem exists_of_lyonsCombination_get_ne_zero {ks : List ℕ} {ws : List LyonsMoments}
    {j : Fin 8} (h : (lyonsCombination ks ws).get j ≠ 0) : ∃ w ∈ ws, w.get j ≠ 0 := by
  induction ws generalizing ks with
  | nil => cases ks <;> simp [lyonsCombination] at h
  | cons w ws ih =>
    cases ks with
    | nil => simp [lyonsCombination] at h
    | cons k ks =>
      simp only [lyonsCombination, get_add, get_smul] at h
      by_cases hw : w.get j = 0
      · rw [hw, mul_zero, zero_add] at h
        obtain ⟨v, hv, hvj⟩ := ih h
        exact ⟨v, List.mem_cons_of_mem _ hv, hvj⟩
      · exact ⟨w, List.mem_cons_self .., hw⟩

theorem mem_lyonsSearch {ws : List LyonsMoments} (hws : ∀ w ∈ ws, w ≠ LyonsMoments.zero)
    {ks : List ℕ} (hlen : ks.length = ws.length) :
    ks ∈ lyonsSearch (lyonsLevels ws) (lyonsCombination ks ws) := by
  induction ws generalizing ks with
  | nil =>
    rw [List.length_nil, List.length_eq_zero_iff] at hlen
    subst hlen
    simp [lyonsLevels, lyonsSearch, lyonsCombination]
  | cons w ws ih =>
    obtain ⟨k, ks, rfl⟩ : ∃ k ks', ks = k :: ks' := by
      cases ks with
      | nil => simp at hlen
      | cons k ks => exact ⟨k, ks, rfl⟩
    simp only [List.length_cons, add_left_inj] at hlen
    have hw : w ≠ LyonsMoments.zero := hws w (List.mem_cons_self ..)
    have ih' := ih (fun v hv => hws v (List.mem_cons_of_mem _ hv)) hlen
    set T := lyonsCombination (k :: ks) (w :: ws) with hT
    have hTget : ∀ j, T.get j = k * w.get j + (lyonsCombination ks ws).get j := by
      intro j
      simp [hT, lyonsCombination]
    have hsupp : T.supported (w.add (lyonsMomentSum ws)) = true := by
      apply supported_eq_true
      intro j hj
      rw [get_add]
      rw [hTget] at hj
      by_cases hwj : w.get j = 0
      · rw [hwj, mul_zero, zero_add] at hj
        obtain ⟨v, hv, hvj⟩ := exists_of_lyonsCombination_get_ne_zero hj
        have := lyonsMomentSum_get_ne_zero hv hvj
        omega
      · omega
    have hk : k ≤ bound w T := le_bound hw fun j => by rw [hTget]; omega
    have hsub : T.sub (w.smul k) = lyonsCombination ks ws := by
      apply ext_get
      intro j
      rw [get_sub, get_smul, hTget]
      omega
    simp only [lyonsLevels, lyonsSearch, hsupp, ite_true, List.mem_flatMap, List.mem_range,
      List.mem_map]
    exact ⟨k, Nat.lt_succ_of_le hk, ks, by rw [hsub]; exact ih', rfl⟩

theorem lyonsCombination_map_get {α : Type*} (l : List α) (f : α → ℕ) (g : α → LyonsMoments)
    (j : Fin 8) :
    (lyonsCombination (l.map f) (l.map g)).get j = (l.map fun x => f x * (g x).get j).sum := by
  induction l with
  | nil => simp [lyonsCombination]
  | cons x l ih => simp [lyonsCombination, ih]

end CFSG.LyonsUnitaryFour
