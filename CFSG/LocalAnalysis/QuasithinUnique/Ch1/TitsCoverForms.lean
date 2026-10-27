module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.QuasithinUnique.Ch1.TitsCover

@[expose] def evalForm (M : ℕ) (c : ℕ → ZMod 2) (f : ℕ) : ZMod 2 :=
  ∑ j ∈ Finset.range M, if f.testBit j then c j else 0

theorem evalForm_zero (M : ℕ) (c : ℕ → ZMod 2) : evalForm M c 0 = 0 := by
  simp [evalForm]

theorem evalForm_xor (M : ℕ) (c : ℕ → ZMod 2) (f g : ℕ) :
    evalForm M c (f ^^^ g) = evalForm M c f + evalForm M c g := by
  unfold evalForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.testBit_xor]
  cases f.testBit j <;> cases g.testBit j <;> simp [CharTwo.add_self_eq_zero]

theorem evalForm_unit {M : ℕ} (c : ℕ → ZMod 2) {e : ℕ} (he : e < M) :
    evalForm M c (2 ^ e) = c e := by
  unfold evalForm
  rw [Finset.sum_eq_single e]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_range.2 he) h

@[expose] def formOf (es : List ℕ) : ℕ := es.foldl (fun f e => f ^^^ 2 ^ e) 0

theorem evalForm_foldl {M : ℕ} (c : ℕ → ZMod 2) (es : List ℕ) (hes : ∀ e ∈ es, e < M) :
    ∀ acc : ℕ, evalForm M c (es.foldl (fun f e => f ^^^ 2 ^ e) acc) =
      evalForm M c acc + (es.map c).sum := by
  induction es with
  | nil => intro acc; simp
  | cons e es ih =>
    intro acc
    have he : e < M := hes e (List.mem_cons_self ..)
    have hes' : ∀ e' ∈ es, e' < M := fun e' h => hes e' (List.mem_cons_of_mem _ h)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih hes', evalForm_xor, evalForm_unit c he]
    ring

theorem evalForm_formOf {M : ℕ} (c : ℕ → ZMod 2) (es : List ℕ) (hes : ∀ e ∈ es, e < M) :
    evalForm M c (formOf es) = (es.map c).sum := by
  rw [formOf, evalForm_foldl c es hes, evalForm_zero, zero_add]

@[expose] def reduceF (piv : Array ℕ) : ℕ → ℕ → ℕ
  | 0, f => f
  | fuel + 1, f =>
    if f = 0 then 0
    else if piv[Nat.log2 f]! = 0 then f
    else reduceF piv fuel (f ^^^ piv[Nat.log2 f]!)

@[expose] def PivSat (M : ℕ) (c : ℕ → ZMod 2) (piv : Array ℕ) : Prop :=
  ∀ k : ℕ, evalForm M c piv[k]! = 0

theorem reduceF_sound {M : ℕ} {c : ℕ → ZMod 2} {piv : Array ℕ} (hp : PivSat M c piv) :
    ∀ (fuel f : ℕ), evalForm M c (reduceF piv fuel f) = evalForm M c f := by
  intro fuel
  induction fuel with
  | zero => intro f; rfl
  | succ fuel ih =>
    intro f
    unfold reduceF
    by_cases h0 : f = 0
    · simp [h0]
    · by_cases hp0 : piv[Nat.log2 f]! = 0
      · simp [h0, hp0]
      · simp only [h0, hp0, ite_false]
        rw [ih, evalForm_xor, hp (Nat.log2 f), add_zero]

@[expose] def insertF (fuel : ℕ) (piv : Array ℕ) (f : ℕ) : Array ℕ :=
  let r := reduceF piv fuel f
  if r = 0 then piv else if Nat.log2 r < piv.size then piv.set! (Nat.log2 r) r else piv

theorem insertF_sound {M : ℕ} {c : ℕ → ZMod 2} {piv : Array ℕ} (hp : PivSat M c piv) (fuel : ℕ)
    {f : ℕ} (hf : evalForm M c f = 0) : PivSat M c (insertF fuel piv f) := by
  unfold insertF
  have hr : evalForm M c (reduceF piv fuel f) = 0 := by rw [reduceF_sound hp, hf]
  by_cases h0 : reduceF piv fuel f = 0
  · simpa [h0] using hp
  · by_cases hlt : Nat.log2 (reduceF piv fuel f) < piv.size
    · simp only [h0, hlt, ite_false, ite_true]
      intro k
      by_cases hk : Nat.log2 (reduceF piv fuel f) = k
      · subst hk
        rw [Array.getElem!_set!_self _ _ _ hlt]
        exact hr
      · rw [Array.getElem!_set!_ne _ _ _ _ hk]
        exact hp k
    · simpa [h0, hlt] using hp

@[expose] def gePivots (fuel M : ℕ) (fs : List ℕ) : Array ℕ :=
  fs.foldl (insertF fuel) (Array.replicate M 0)

theorem pivSat_replicate (M : ℕ) (c : ℕ → ZMod 2) (N : ℕ) : PivSat M c (Array.replicate N 0) := by
  intro k
  by_cases hk : k < N
  · simp [hk, evalForm_zero]
  · simp [hk, evalForm_zero]

theorem foldl_insertF_sound {M : ℕ} {c : ℕ → ZMod 2} (fuel : ℕ) (fs : List ℕ)
    (hfs : ∀ f ∈ fs, evalForm M c f = 0) :
    ∀ piv : Array ℕ, PivSat M c piv → PivSat M c (fs.foldl (insertF fuel) piv) := by
  induction fs with
  | nil => intro piv hp; exact hp
  | cons f fs ih =>
    intro piv hp
    exact ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) _
      (insertF_sound hp fuel (hfs f (List.mem_cons_self ..)))

theorem gePivots_sound {M : ℕ} {c : ℕ → ZMod 2} (fuel : ℕ) {fs : List ℕ}
    (hfs : ∀ f ∈ fs, evalForm M c f = 0) : PivSat M c (gePivots fuel M fs) :=
  foldl_insertF_sound fuel fs hfs _ (pivSat_replicate M c M)

theorem eq_zero_of_reduce {M : ℕ} {c : ℕ → ZMod 2} (fuel : ℕ) {fs : List ℕ}
    (hfs : ∀ f ∈ fs, evalForm M c f = 0) {e : ℕ} (he : e < M)
    (hred : reduceF (gePivots fuel M fs) fuel (2 ^ e) = 0) : c e = 0 := by
  have h := reduceF_sound (gePivots_sound fuel hfs) fuel (2 ^ e)
  rw [hred, evalForm_zero, evalForm_unit c he] at h
  exact h.symm

end CFSG.QuasithinUnique.Ch1.TitsCover
