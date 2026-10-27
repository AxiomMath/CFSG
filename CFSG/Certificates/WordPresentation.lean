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
public import Mathlib.GroupTheory.PresentedGroup
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

public section

namespace CFSG.Certificates

variable {m : ℕ}

@[expose] def wordRels (ws : List (List (Fin m × Bool))) : Set (FreeGroup (Fin m)) :=
  {r | ∃ w ∈ ws, FreeGroup.mk w = r}

@[expose] def signedProd {G : Type*} [Group G] (x : Fin m → G) (w : List (Fin m × Bool)) : G :=
  (w.map fun l => if l.2 then x l.1 else (x l.1)⁻¹).prod

@[simp] theorem signedProd_nil {G : Type*} [Group G] (x : Fin m → G) : signedProd x [] = 1 := rfl

theorem signedProd_cons {G : Type*} [Group G] (x : Fin m → G) (l : Fin m × Bool)
    (w : List (Fin m × Bool)) :
    signedProd x (l :: w) = (if l.2 then x l.1 else (x l.1)⁻¹) * signedProd x w := by
  simp [signedProd]

theorem signedProd_append {G : Type*} [Group G] (x : Fin m → G) (u v : List (Fin m × Bool)) :
    signedProd x (u ++ v) = signedProd x u * signedProd x v := by
  simp [signedProd]

theorem map_signedProd {G H : Type*} [Group G] [Group H] (φ : G →* H) (x : Fin m → G)
    (w : List (Fin m × Bool)) : φ (signedProd x w) = signedProd (fun i => φ (x i)) w := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [signedProd_cons, signedProd_cons, map_mul, ih]
    split <;> simp

theorem signedProd_mem {G : Type*} [Group G] {K : Subgroup G} {x : Fin m → G} (hx : ∀ i, x i ∈ K)
    (w : List (Fin m × Bool)) : signedProd x w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [signedProd_cons]
    refine K.mul_mem ?_ ih
    split
    · exact hx _
    · exact K.inv_mem (hx _)

theorem signedProd_replicate {G : Type*} [Group G] (x : Fin m → G) (k : ℕ)
    (w : List (Fin m × Bool)) : signedProd x (List.replicate k w).flatten = signedProd x w ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, signedProd_append, ih, pow_succ']

theorem lift_mk_eq_signedProd {G : Type*} [Group G] (x : Fin m → G) (w : List (Fin m × Bool)) :
    FreeGroup.lift x (FreeGroup.mk w) = signedProd x w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul, ih,
      signedProd_cons]
    obtain ⟨i, b⟩ := l
    cases b with
    | true =>
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      rfl
    | false =>
      rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      rfl

theorem signedProd_of (ws : List (List (Fin m × Bool))) (w : List (Fin m × Bool)) :
    signedProd (PresentedGroup.of (rels := wordRels ws)) w =
      PresentedGroup.mk (wordRels ws) (FreeGroup.mk w) := by
  rw [← lift_mk_eq_signedProd]
  induction FreeGroup.mk w using FreeGroup.induction_on with
  | one => simp
  | of i => simp [PresentedGroup.of]
  | inv_of i _ => simp [PresentedGroup.of]
  | mul a b ha hb => rw [map_mul, ha, hb, map_mul]

theorem signedProd_of_eq_one {ws : List (List (Fin m × Bool))} {w : List (Fin m × Bool)}
    (hw : w ∈ ws) : signedProd (PresentedGroup.of (rels := wordRels ws)) w = 1 := by
  rw [signedProd_of]
  exact PresentedGroup.one_of_mem ⟨w, hw, rfl⟩

noncomputable def wordsHom {G : Type*} [Group G] (ws : List (List (Fin m × Bool))) (x : Fin m → G)
    (h : ∀ w ∈ ws, signedProd x w = 1) : PresentedGroup (wordRels ws) →* G :=
  PresentedGroup.toGroup (f := x) (by
    rintro r ⟨w, hw, rfl⟩
    rw [lift_mk_eq_signedProd]
    exact h w hw)

@[simp] theorem wordsHom_of {G : Type*} [Group G] (ws : List (List (Fin m × Bool)))
    (x : Fin m → G) (h : ∀ w ∈ ws, signedProd x w = 1) (i : Fin m) :
    wordsHom ws x h (PresentedGroup.of i) = x i :=
  PresentedGroup.toGroup.of _

theorem wordsHom_signedProd {G : Type*} [Group G] (ws : List (List (Fin m × Bool)))
    (x : Fin m → G) (h : ∀ w ∈ ws, signedProd x w = 1) (w : List (Fin m × Bool)) :
    wordsHom ws x h (signedProd PresentedGroup.of w) = signedProd x w := by
  rw [map_signedProd]
  simp

theorem range_wordsHom {G : Type*} [Group G] (ws : List (List (Fin m × Bool))) (x : Fin m → G)
    (h : ∀ w ∈ ws, signedProd x w = 1) :
    (wordsHom ws x h).range = Subgroup.closure (Set.range x) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext i
  simp

theorem signedProd_neg_one (w : List (Fin m × Bool)) :
    signedProd (fun _ => (-1 : ℤˣ)) w = (-1) ^ w.length := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [signedProd_cons, ih, List.length_cons, pow_succ']
    split <;> simp

end CFSG.Certificates
