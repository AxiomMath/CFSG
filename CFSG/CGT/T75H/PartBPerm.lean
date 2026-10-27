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
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.T75H.PermModel

open Equiv

@[expose] def cmp (σ τ : List ℕ) : List ℕ := τ.map fun i => σ.getD i 0

@[expose] def idl (n : ℕ) : List ℕ := List.range n

@[expose] def moved (n : ℕ) (σ : List ℕ) : ℕ :=
  ((List.range n).filter fun i => σ.getD i 0 ≠ i).length

@[expose] def enc {n : ℕ} (σ : Perm (Fin n)) : List ℕ := (List.finRange n).map fun i => (σ i : ℕ)

theorem enc_getD {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) : (enc σ).getD i 0 = (σ i : ℕ) := by
  simp [enc, List.getD_eq_getElem?_getD]

theorem enc_mul {n : ℕ} (σ τ : Perm (Fin n)) : enc (σ * τ) = cmp (enc σ) (enc τ) := by
  simp only [enc, cmp, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Perm.coe_mul]
  rw [← enc_getD σ (τ i)]
  rfl

theorem enc_one {n : ℕ} : enc (1 : Perm (Fin n)) = idl n := by
  simp [enc, idl, List.map_coe_finRange_eq_range]

theorem enc_injective {n : ℕ} : Function.Injective (enc : Perm (Fin n) → List ℕ) := by
  intro σ τ h
  ext i
  have h1 := enc_getD σ i
  have h2 := enc_getD τ i
  rw [h] at h1
  exact h1.symm.trans h2

theorem enc_mem_permutations {n : ℕ} (σ : Perm (Fin n)) :
    enc σ ∈ (List.range n).permutations' := by
  rw [List.mem_permutations']
  have h := (Equiv.Perm.map_finRange_perm σ).map (fun i : Fin n => (i : ℕ))
  rw [List.map_map, List.map_coe_finRange_eq_range] at h
  exact h

theorem moved_enc {n : ℕ} (σ : Perm (Fin n)) : moved n (enc σ) = σ.support.card := by
  classical
  have h1 : (List.range n) = (List.finRange n).map (fun i : Fin n => (i : ℕ)) :=
    List.map_coe_finRange_eq_range.symm
  unfold moved
  rw [h1, List.filter_map, List.length_map]
  have h2 : (List.finRange n).filter ((fun i : ℕ => decide ((enc σ).getD i 0 ≠ i)) ∘
      (fun i : Fin n => (i : ℕ))) = (List.finRange n).filter (fun i => decide (σ i ≠ i)) := by
    apply List.filter_congr
    intro i _
    simp only [Function.comp_apply, enc_getD, ne_eq]
    simp [Fin.ext_iff]
  rw [h2]
  have h3 : σ.support = Finset.univ.filter (fun i => σ i ≠ i) := by
    ext i
    simp
  have key : ∀ l : List (Fin n), l.countP (fun i => decide (σ i ≠ i)) =
      (l.map (fun i => if σ i ≠ i then 1 else 0)).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
      by_cases ha : σ a = a
      · simp [ha]
      · simp [ha, add_comm]
  rw [h3, Finset.card_filter, Fin.sum_univ_def, ← List.countP_eq_length_filter, key]

@[expose] def c1 (n : ℕ) : List ℕ :=
  (List.range n).map fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else i

@[expose] def c2 (n : ℕ) : List ℕ :=
  (List.range n).map fun i => if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 3 else i

@[expose] def ppow (n : ℕ) (c : List ℕ) (i : ℕ) : List ℕ :=
  if i = 0 then idl n else if i = 1 then c else cmp c c

@[expose] def qlist (n i j : ℕ) : List ℕ := cmp (ppow n (c1 n) i) (ppow n (c2 n) j)

@[expose] def cj (q a : List ℕ) : List ℕ := cmp (cmp (cmp q q) a) q

@[expose] def Fl2List (n : ℕ) : Prop :=
  ∀ l ∈ (List.range n).permutations', moved n l = 4 → cmp l l = idl n →
    cmp (cmp l (c1 n)) l = cmp (c1 n) (c1 n) → cmp (cmp l (c2 n)) l = cmp (c2 n) (c2 n) →
    ∀ y ∈ (List.range n).permutations', moved n y = 4 → cmp y y = idl n →
      cmp l y = cmp y l → y ≠ l →
      ∃ i ∈ List.range 3, ∃ j ∈ List.range 3,
        ¬ ((cmp y (cj (qlist n i j) y) = cmp (cj (qlist n i j) y) y) ↔
          (cmp (cmp y l) (cj (qlist n i j) (cmp y l)) =
            cmp (cj (qlist n i j) (cmp y l)) (cmp y l)))

set_option maxRecDepth 100000 in
theorem fl2List_six : Fl2List 6 := by
  unfold Fl2List
  decide +kernel

set_option maxRecDepth 100000 in
theorem fl2List_seven : Fl2List 7 := by
  unfold Fl2List
  decide +kernel

end CFSG.CGT.T75H.PermModel
