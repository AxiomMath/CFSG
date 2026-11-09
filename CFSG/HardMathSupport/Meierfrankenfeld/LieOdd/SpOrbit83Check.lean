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
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.SortCheck

public section

open Matrix

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

@[expose] def Afam : Fin 29 → Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  ![
  !![2, 0, 1, 0; 1, 0, 2, 1; 1, 2, 2, 0; 2, 2, 0, 2],
  !![2, 2, 2, 0; 1, 2, 0, 1; 0, 1, 1, 2; 0, 1, 0, 1],
  !![1, 0, 2, 2; 1, 1, 0, 2; 0, 1, 0, 2; 2, 1, 2, 0],
  !![2, 2, 0, 1; 0, 2, 1, 1; 2, 2, 2, 1; 1, 2, 1, 2],
  !![0, 0, 1, 1; 0, 0, 0, 2; 1, 0, 0, 1; 1, 2, 2, 1],
  !![0, 2, 0, 0; 2, 2, 0, 2; 2, 0, 1, 0; 1, 0, 2, 2],
  !![1, 0, 2, 1; 0, 0, 1, 0; 1, 1, 2, 0; 0, 2, 1, 0],
  !![2, 2, 1, 0; 2, 2, 2, 2; 2, 0, 0, 0; 1, 2, 0, 0],
  !![0, 2, 2, 2; 2, 0, 1, 0; 1, 0, 0, 2; 1, 2, 1, 0],
  !![2, 1, 2, 2; 2, 2, 0, 0; 0, 1, 1, 0; 0, 2, 1, 2],
  !![0, 1, 2, 1; 1, 1, 0, 1; 1, 2, 2, 0; 0, 1, 1, 0],
  !![2, 1, 2, 2; 2, 2, 2, 2; 2, 1, 1, 0; 2, 0, 1, 2],
  !![0, 1, 0, 2; 1, 1, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0],
  !![2, 1, 1, 2; 2, 1, 0, 1; 1, 2, 1, 1; 1, 0, 1, 1],
  !![2, 0, 1, 2; 1, 2, 2, 1; 0, 2, 1, 2; 2, 0, 0, 1],
  !![2, 1, 0, 0; 0, 0, 0, 1; 0, 1, 0, 1; 2, 2, 2, 0],
  !![2, 0, 2, 0; 2, 2, 0, 2; 1, 1, 2, 2; 2, 0, 0, 1],
  !![1, 0, 0, 0; 2, 1, 2, 0; 1, 2, 2, 1; 1, 2, 1, 2],
  !![0, 1, 2, 0; 0, 2, 2, 0; 2, 1, 1, 1; 1, 1, 2, 1],
  !![1, 2, 1, 1; 1, 0, 0, 1; 0, 1, 2, 2; 1, 0, 1, 1],
  !![1, 2, 0, 0; 2, 1, 2, 0; 0, 0, 0, 1; 2, 0, 1, 0],
  !![0, 1, 2, 1; 1, 0, 2, 2; 0, 1, 0, 1; 2, 0, 1, 0],
  !![2, 1, 2, 1; 1, 0, 1, 2; 2, 0, 2, 0; 1, 2, 2, 0],
  !![2, 1, 2, 0; 1, 1, 1, 0; 2, 0, 1, 0; 0, 2, 1, 1],
  !![0, 1, 2, 2; 1, 0, 2, 1; 0, 0, 1, 0; 1, 0, 0, 2],
  !![0, 1, 1, 0; 0, 2, 1, 1; 2, 0, 1, 1; 0, 2, 2, 1],
  !![0, 2, 0, 1; 1, 0, 1, 2; 2, 1, 0, 0; 0, 2, 0, 2],
  !![2, 0, 2, 2; 2, 1, 2, 2; 1, 0, 0, 2; 0, 0, 0, 2],
  !![1, 2, 2, 0; 0, 1, 2, 2; 2, 1, 2, 1; 0, 2, 0, 1]
  ]

theorem Afam_det : ∀ i, (Afam i).det ≠ 0 := by
  decide +kernel

theorem form_ne_zero : ∀ a b c d : ZMod 3, ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) →
    ∀ i : Fin 29, Afam i * Matrix.diagonal ![a, b, c, d] * (Afam i)ᵀ ≠ 0 := by
  decide +kernel

@[expose] def pform (a b c d : ZMod 3) (i : Fin 29) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Afam i * Matrix.diagonal ![a, b, c, d] * (Afam i)ᵀ

@[expose] def fkey (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) : List (ZMod 3) :=
  (List.finRange 4).flatMap fun x => (List.finRange 4).map fun y => M x y

@[expose] def fcode (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) : ℕ :=
  (fkey M).foldr (fun x acc => x.val + 3 * acc) 0

@[expose] def colM (i : Fin 29) (t : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.vecMulVec (fun x => Afam i x t) (fun y => Afam i y t)

@[expose] def lform (a b c d : ZMod 3) (i : Fin 29) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  a • colM i 0 + b • colM i 1 + c • colM i 2 + d • colM i 3

theorem pform_eq_lform (a b c d : ZMod 3) (i : Fin 29) : pform a b c d i = lform a b c d i := by
  ext x y
  rw [pform, Matrix.mul_apply]
  simp [Matrix.mul_diagonal, Fin.sum_univ_four, lform, colM, Matrix.vecMulVec_apply] <;> ring

@[expose] def formCodes (a b c d : ZMod 3) : List ℕ :=
  (List.finRange 29).flatMap fun i =>
    [fcode (lform a b c d i), fcode ((2 : ZMod 3) • lform a b c d i)]

theorem formCodes_sorted : ∀ a b c d : ZMod 3, ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) →
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.strictB
      (CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.msortN (formCodes a b c d)) = true := by
  decide +kernel

theorem pairwise_forall_of_symm {α : Type*} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.mem_cons] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · subst ha
      exact h1 b hb
    · subst hb
      exact hR _ _ (h1 a ha)
    · exact ih h2 a ha b hb hab

theorem pair_distinct : ∀ a b c d : ZMod 3, ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) →
    ∀ i j : Fin 29, i ≠ j → ∀ k : ZMod 3,
      Afam j * Matrix.diagonal ![a, b, c, d] * (Afam j)ᵀ ≠
        k • (Afam i * Matrix.diagonal ![a, b, c, d] * (Afam i)ᵀ) := by
  intro a b c d h0 i j hij k
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by revert k; decide
  intro hk
  change pform a b c d j = k • pform a b c d i at hk
  have hnd := CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.nodup_of_strictB
    (formCodes_sorted a b c d h0)
  rw [formCodes, List.nodup_flatMap] at hnd
  have hd : List.Disjoint [fcode (lform a b c d i), fcode ((2 : ZMod 3) • lform a b c d i)]
      [fcode (lform a b c d j), fcode ((2 : ZMod 3) • lform a b c d j)] :=
    pairwise_forall_of_symm (fun _ _ h => List.Disjoint.symm h) _ hnd.2 i (List.mem_finRange i) j
      (List.mem_finRange j) hij
  rcases hk3 with rfl | rfl | rfl
  · rw [zero_smul] at hk
    exact form_ne_zero a b c d h0 j hk
  · rw [one_smul, pform_eq_lform, pform_eq_lform] at hk
    exact hd (a := fcode (lform a b c d i)) (by simp) (by simp [hk])
  · rw [pform_eq_lform, pform_eq_lform] at hk
    exact hd (a := fcode ((2 : ZMod 3) • lform a b c d i)) (by simp) (by simp [hk])

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
