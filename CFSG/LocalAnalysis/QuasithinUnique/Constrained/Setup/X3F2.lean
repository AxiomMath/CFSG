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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.QuasithinUnique.Setup.X3E

open Finset

abbrev Vec (d : ℕ) : Type := Fin d → ZMod 2

@[expose] def toVec (d x : ℕ) : Vec d := fun j => if x.testBit j.val then 1 else 0

theorem toVec_apply (d x : ℕ) (j : Fin d) : toVec d x j = if x.testBit j.val then 1 else 0 := rfl

theorem toVec_xor (d x y : ℕ) : toVec d (x ^^^ y) = toVec d x + toVec d y := by
  funext j
  simp only [toVec, Nat.testBit_xor, Pi.add_apply]
  cases x.testBit j.val <;> cases y.testBit j.val <;> decide

theorem toVec_zero (d : ℕ) : toVec d 0 = 0 := by
  funext j; simp [toVec]

theorem toVec_injOn {d x y : ℕ} (hx : x < 2 ^ d) (hy : y < 2 ^ d) (h : toVec d x = toVec d y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < d
  · have := congrFun h ⟨j, hj⟩
    simp only [toVec] at this
    cases hxj : x.testBit j <;> cases hyj : y.testBit j <;> simp_all
  · have hle : 2 ^ d ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hle)]

@[expose] def ofBits (d : ℕ) (f : ℕ → Bool) : ℕ :=
  (List.range d).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0

theorem ofBits_testBit (d : ℕ) (f : ℕ → Bool) (i : ℕ) :
    (ofBits d f).testBit i = (decide (i < d) && f i) := by
  unfold ofBits
  induction d with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split_ifs with hf
    · rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases him : i = m
      · subst him; simp [hf]
      · have h1 : (i < m + 1) ↔ (i < m) := by omega
        simp [h1, Ne.symm him]
    · rw [ih]
      by_cases him : i = m
      · subst him; simp [hf]
      · have h1 : (i < m + 1) ↔ (i < m) := by omega
        simp [h1]

theorem ofBits_lt (d : ℕ) (f : ℕ → Bool) : ofBits d f < 2 ^ d := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [ofBits_testBit]
  simp; omega

theorem toVec_ofBits (d : ℕ) (f : ℕ → Bool) (j : Fin d) :
    toVec d (ofBits d f) j = if f j.val then 1 else 0 := by
  rw [toVec_apply, ofBits_testBit]
  simp [j.isLt]

theorem exists_toVec {d : ℕ} (v : Vec d) : ∃ x, x < 2 ^ d ∧ toVec d x = v := by
  classical
  refine ⟨ofBits d fun j => if h : j < d then decide (v ⟨j, h⟩ = 1) else false, ofBits_lt _ _, ?_⟩
  funext j
  rw [toVec_ofBits]
  simp only [j.isLt, dite_true]
  have : v j = 0 ∨ v j = 1 := by
    generalize v j = a
    revert a; decide
  rcases this with h | h <;> simp [h]

theorem toVec_one_shiftLeft (d k : ℕ) (hk : k < d) :
    toVec d (1 <<< k) = Pi.single ⟨k, hk⟩ (1 : ZMod 2) := by
  funext j
  rw [toVec_apply, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : j = ⟨k, hk⟩
  · subst h; simp
  · have h' : k ≠ j.val := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem foldl_xor_toVec (d : ℕ) (P : ℕ → Prop) [DecidablePred P] (g : ℕ → ℕ) (m init : ℕ) :
    toVec d ((List.range m).foldl (fun acc i => if P i then acc ^^^ g i else acc) init) =
      toVec d init + ∑ i ∈ range m, if P i then toVec d (g i) else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ,
      ← add_assoc, ← ih]
    split_ifs <;> simp [toVec_xor]

@[expose] def papply (d : ℕ) (cols : List ℕ) (v : ℕ) : ℕ :=
  (List.range d).foldl (fun acc j => if v.testBit j then acc ^^^ cols.getD j 0 else acc) 0

@[expose] noncomputable def lin (d : ℕ) (cols : List ℕ) : Vec d →ₗ[ZMod 2] Vec d :=
  Fintype.linearCombination (ZMod 2) (fun j : Fin d => toVec d (cols.getD j.val 0))

theorem lin_apply (d : ℕ) (cols : List ℕ) (v : Vec d) :
    lin d cols v = ∑ j : Fin d, v j • toVec d (cols.getD j.val 0) := rfl

theorem toVec_papply (d : ℕ) (cols : List ℕ) (v : ℕ) :
    toVec d (papply d cols v) = lin d cols (toVec d v) := by
  unfold papply
  rw [foldl_xor_toVec d (fun j => v.testBit j = true) (fun j => cols.getD j 0), toVec_zero, zero_add,
    lin_apply, ← Fin.sum_univ_eq_sum_range (fun i =>
      if v.testBit i = true then toVec d (cols.getD i 0) else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toVec_apply]
  split_ifs <;> simp

theorem papply_lt {d n : ℕ} {cols : List ℕ} (h : ∀ j < d, cols.getD j 0 < 2 ^ n) (v : ℕ) :
    papply d cols v < 2 ^ n := by
  unfold papply
  suffices hs : ∀ m ≤ d, ∀ init, init < 2 ^ n →
      (List.range m).foldl (fun acc j => if v.testBit j then acc ^^^ cols.getD j 0 else acc) init
        < 2 ^ n by
    exact hs d le_rfl 0 (by positivity)
  intro m
  induction m with
  | zero => intro _ init hi; simpa using hi
  | succ m ih =>
    intro hm init hi
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h1 := ih (by omega) init hi
    split_ifs
    · exact Nat.xor_lt_two_pow h1 (h m (by omega))
    · exact h1

@[expose] def wapp (d : ℕ) (cols : Bool → List ℕ) (w : List Bool) (v : ℕ) : ℕ :=
  w.foldr (fun b acc => papply d (cols b) acc) v

@[expose] noncomputable def wmap {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (g : Bool → (M →ₗ[ZMod 2] M)) : List Bool → (M →ₗ[ZMod 2] M)
  | [] => LinearMap.id
  | b :: w => g b ∘ₗ wmap g w

theorem toVec_wapp (d : ℕ) (cols : Bool → List ℕ) (w : List Bool) (v : ℕ) :
    toVec d (wapp d cols w v) = (wmap (fun b => lin d (cols b)) w) (toVec d v) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    unfold wapp at ih ⊢
    simp only [List.foldr_cons]
    rw [toVec_papply, ih]
    rfl

theorem wmap_cons {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (g : Bool → (M →ₗ[ZMod 2] M)) (b : Bool) (w : List Bool) (v : M) :
    (wmap g (b :: w)) v = g b ((wmap g w) v) := rfl

theorem wmap_intertwine {M N : Type*} [AddCommMonoid M] [Module (ZMod 2) M] [AddCommMonoid N]
    [Module (ZMod 2) N] (gM : Bool → (M →ₗ[ZMod 2] M)) (gN : Bool → (N →ₗ[ZMod 2] N))
    (φ : M →ₗ[ZMod 2] N) (h : ∀ b v, φ (gM b v) = gN b (φ v)) :
    ∀ (w : List Bool) (v : M), φ ((wmap gM w) v) = (wmap gN w) (φ v)
  | [], v => rfl
  | b :: w, v => by
    rw [wmap_cons, h, wmap_intertwine gM gN φ h w v]
    rfl

@[expose] def dotb (d ψ v : ℕ) : Bool :=
  (List.range d).foldl (fun acc k => xor acc (ψ.testBit k && v.testBit k)) false

@[expose] noncomputable def fnl (d ψ : ℕ) : Vec d →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ k, toVec d ψ k * v k
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_left_comm]

theorem fnl_apply (d ψ : ℕ) (v : Vec d) : fnl d ψ v = ∑ k, toVec d ψ k * v k := rfl

theorem castBool_xor_and (c a b : Bool) :
    (if xor c (a && b) then (1 : ZMod 2) else 0) =
      (if c then 1 else 0) + (if a then 1 else 0) * (if b then 1 else 0) := by
  cases c <;> cases a <;> cases b <;> decide

theorem foldl_dotb_cast (ψ v : ℕ) (m : ℕ) (b : Bool) :
    ((if (List.range m).foldl (fun acc k => xor acc (ψ.testBit k && v.testBit k)) b then 1 else 0 :
        ZMod 2)) =
      (if b then 1 else 0) + ∑ k ∈ range m,
        (if ψ.testBit k then (1 : ZMod 2) else 0) * (if v.testBit k then (1 : ZMod 2) else 0) := by
  induction m generalizing b with
  | zero => cases b <;> simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ,
      ← add_assoc, ← ih]
    exact castBool_xor_and _ _ _

theorem dotb_cast (d ψ v : ℕ) :
    ((if dotb d ψ v then 1 else 0 : ZMod 2)) = fnl d ψ (toVec d v) := by
  unfold dotb
  rw [foldl_dotb_cast, fnl_apply]
  simp only [Bool.false_eq_true, ite_false, zero_add]
  rw [← Fin.sum_univ_eq_sum_range (fun k =>
    (if ψ.testBit k then (1 : ZMod 2) else 0) * (if v.testBit k then (1 : ZMod 2) else 0)) d]
  rfl

end CFSG.QuasithinUnique.Setup.X3E
