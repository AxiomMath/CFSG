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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

namespace CFSG.LargeExtraspecial.FS77

abbrev V6 := Fin 6 → ZMod 2

@[expose] def beta6 (v w : V6) : ZMod 2 :=
  v 4 * w 4 + v 5 * w 5 + v 1 * w 0 + v 3 * w 2 + v 5 * w 4

@[expose] def q6 (v : V6) : ZMod 2 := v 0 * v 1 + v 2 * v 3 + v 4 + v 4 * v 5 + v 5

@[expose] def polar6 (v w : V6) : ZMod 2 :=
  v 0 * w 1 + v 1 * w 0 + v 2 * w 3 + v 3 * w 2 + v 4 * w 5 + v 5 * w 4

@[expose] def tMat : Fin 3 → Matrix (Fin 6) (Fin 6) (ZMod 2)
  | 0 => !![1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 1, 1, 1, 1, 0; 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1]
  | 1 => !![1, 1, 0, 1, 0, 1; 0, 1, 0, 0, 0, 0; 0, 1, 1, 1, 0, 1; 0, 0, 0, 1, 0, 0;
      0, 1, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1]
  | 2 => !![1, 1, 0, 0, 1, 1; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1]

@[expose] def tLin (k : Fin 3) : V6 →ₗ[ZMod 2] V6 := Matrix.mulVecLin (tMat k)

@[expose] def tComp : List (Fin 3) → V6 → V6
  | [], v => v
  | k :: ks, v => tLin k (tComp ks v)

@[expose] def wordSum (F : Fin 3 → V6 → ZMod 2) : List (Fin 3) → V6 → ZMod 2
  | [], _ => 0
  | k :: ks, v => F k (tComp ks v) + wordSum F ks v

namespace Core

theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by
  revert x
  decide

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

end Core

theorem tMat_two_two : tMat 2 * tMat 2 = 1 := by
  decide +kernel

theorem tMat_w1 : tMat 0 * tMat 1 * tMat 0 * tMat 2 * tMat 1 * tMat 2 = 1 := by
  decide +kernel

theorem tMat_w2 : tMat 0 * tMat 1 * tMat 2 * tMat 0 * tMat 2 * tMat 1 = 1 := by
  decide +kernel

theorem tComp_two_two (v : V6) : tComp [2, 2] v = v := by
  simp only [tComp, tLin, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, tMat_two_two,
    Matrix.one_mulVec]

theorem tComp_w1 (v : V6) : tComp [0, 1, 0, 2, 1, 2] v = v := by
  simp only [tComp, tLin, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    tMat_w1, Matrix.one_mulVec]

theorem tComp_w2 (v : V6) : tComp [0, 1, 2, 0, 2, 1] v = v := by
  simp only [tComp, tLin, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    tMat_w2, Matrix.one_mulVec]

namespace Core

@[expose] def betaDefect (k : Fin 3) (v w : V6) : ZMod 2 :=
  beta6 (tLin k v) (tLin k w) + beta6 v w

@[expose] def defectSum (k : Fin 3) : List V6 → ZMod 2
  | [] => 0
  | a :: l => betaDefect k a l.sum + defectSum k l

@[expose] def coordParts (v : V6) : List V6 := List.ofFn fun i => Pi.single i (v i)

@[expose] def quadPart (k : Fin 3) (v : V6) : ZMod 2 := defectSum k (coordParts v)

theorem coordParts_sum (v : V6) : (coordParts v).sum = v := by
  rw [coordParts, List.sum_ofFn]
  exact Finset.univ_sum_single v

abbrev AffRow := (Fin 3 → Fin 6 → ZMod 2) × ZMod 2

@[expose] def affEval (c : Fin 3 → Fin 6 → ZMod 2) (r : AffRow) : ZMod 2 :=
  ∑ k, ∑ i, r.1 k i * c k i + r.2

@[expose] def affOfF (k : Fin 3) (v : V6) : AffRow := (Pi.single k v, quadPart k v)

@[expose] def wordAff : List (Fin 3) → V6 → AffRow
  | [], _ => 0
  | k :: ks, v => affOfF k (tComp ks v) + wordAff ks v

theorem affEval_add (c : Fin 3 → Fin 6 → ZMod 2) (r s : AffRow) :
    affEval c (r + s) = affEval c r + affEval c s := by
  simp only [affEval, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem affEval_affOfF (c : Fin 3 → Fin 6 → ZMod 2) (k : Fin 3) (v : V6) :
    affEval c (affOfF k v) = ∑ i, v i * c k i + quadPart k v := by
  simp only [affEval, affOfF]
  congr 1
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

theorem wordAff_certificate :
    wordAff [2, 2] (Pi.single 1 1) + wordAff [0, 1, 0, 2, 1, 2] (Pi.single 1 1) +
      wordAff [0, 1, 0, 2, 1, 2] (Pi.single 5 1) + wordAff [0, 1, 2, 0, 2, 1] (Pi.single 1 1) +
      wordAff [0, 1, 2, 0, 2, 1] (Pi.single 3 1) = (0, 1) := by
  decide +kernel

section Expansion

variable {F : Fin 3 → V6 → ZMod 2}
  (hF : ∀ k v w, F k (v + w) = F k v + F k w + beta6 (tLin k v) (tLin k w) + beta6 v w)
include hF

theorem cocycle_zero (k : Fin 3) : F k 0 = 0 := by
  have h := hF k 0 0
  have h0 : beta6 0 0 = 0 := by decide
  rw [add_zero, map_zero, h0] at h
  linear_combination -h

theorem cocycle_add (k : Fin 3) (v w : V6) : F k (v + w) = F k v + F k w + betaDefect k v w := by
  rw [hF, betaDefect]
  ring

theorem cocycle_list_sum (k : Fin 3) :
    ∀ l : List V6, F k l.sum = (l.map (F k)).sum + defectSum k l
  | [] => by simp [cocycle_zero hF, defectSum]
  | a :: l => by
    rw [List.sum_cons, cocycle_add hF, cocycle_list_sum k l, List.map_cons, List.sum_cons,
      defectSum]
    ring

theorem cocycle_single (k : Fin 3) (i : Fin 6) (a : ZMod 2) :
    F k (Pi.single i a) = a * F k (Pi.single i 1) := by
  rcases zmod2_cases a with rfl | rfl
  · rw [Pi.single_zero, cocycle_zero hF, zero_mul]
  · rw [one_mul]

theorem cocycle_eq (k : Fin 3) (v : V6) :
    F k v = ∑ i, v i * F k (Pi.single i 1) + quadPart k v := by
  have h := cocycle_list_sum hF k (coordParts v)
  rw [coordParts_sum] at h
  rw [h, quadPart, coordParts, List.map_ofFn, List.sum_ofFn]
  congr 1
  exact Finset.sum_congr rfl fun i _ => cocycle_single hF k i (v i)

theorem wordSum_eq_affEval : ∀ (ω : List (Fin 3)) (v : V6),
    wordSum F ω v = affEval (fun k i => F k (Pi.single i 1)) (wordAff ω v)
  | [], v => by simp [wordSum, wordAff, affEval]
  | k :: ks, v => by
    rw [wordSum, wordAff, affEval_add, affEval_affOfF, ← cocycle_eq hF,
      wordSum_eq_affEval ks v]

end Expansion

end Core

theorem core_obstruction (F : Fin 3 → V6 → ZMod 2)
    (hF : ∀ k v w, F k (v + w) = F k v + F k w + beta6 (tLin k v) (tLin k w) + beta6 v w)
    (h3 : ∀ v, wordSum F [2, 2] v = 0)
    (hw1 : ∀ v, wordSum F [0, 1, 0, 2, 1, 2] v = 0)
    (hw2 : ∀ v, wordSum F [0, 1, 2, 0, 2, 1] v = 0) : False := by
  have h := congrArg (Core.affEval fun k i => F k (Pi.single i 1)) Core.wordAff_certificate
  simp only [Core.affEval_add, ← Core.wordSum_eq_affEval hF, h3, hw1, hw2, add_zero] at h
  have h1 : Core.affEval (fun k i => F k (Pi.single i 1)) (0, 1) = 1 := by simp [Core.affEval]
  exact absurd (h.trans h1) (by decide)

end CFSG.LargeExtraspecial.FS77
