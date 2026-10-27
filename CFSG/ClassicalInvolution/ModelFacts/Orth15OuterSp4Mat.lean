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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4

open Matrix

variable {F : Type} [Field F]

theorem map_transvection {κ : Type*} [DecidableEq κ] (σ : F ≃+* F) (p q : κ) (t : F) :
    (Matrix.transvection p q t).map σ = Matrix.transvection p q (σ t) := by
  ext a b
  simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.one_apply]
  split_ifs <;> simp

theorem rel_facts {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ} (σ : F ≃+* F)
    (A : Matrix κ κ F) (t : F) (ht : t ≠ 0)
    (h : A * Matrix.transvection p q (σ t) = Matrix.transvection p q t * A) :
    (∀ b, b ≠ q → A q b = 0) ∧ (∀ a, a ≠ p → A a p = 0) ∧ A p p * σ t = t * A q q := by
  have hσt : σ t ≠ 0 := (map_ne_zero σ).mpr ht
  refine ⟨fun b hb => ?_, fun a ha => ?_, ?_⟩
  · have e := congrFun (congrFun h p) b
    rw [Matrix.mul_transvection_apply_of_ne p q _ _ hb, Matrix.transvection_mul_apply_same] at e
    have : t * A q b = 0 := by linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left ht
  · have e := congrFun (congrFun h a) q
    rw [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_of_ne p q a q ha] at e
    have : σ t * A a p = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_left hσt
  · have e := congrFun (congrFun h p) q
    rw [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same] at e
    linear_combination e

theorem sp4_shape (σ : F ≃+* F) (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (hdet : A.det ≠ 0)
    (hu : ∀ (k : Fin 2) (t : F), A * Matrix.transvection (Sum.inl k) (Sum.inr k) (σ t) =
      Matrix.transvection (Sum.inl k) (Sum.inr k) t * A)
    (hl : ∀ (k : Fin 2) (t : F), A * Matrix.transvection (Sum.inr k) (Sum.inl k) (σ t) =
      Matrix.transvection (Sum.inr k) (Sum.inl k) t * A) :
    σ = RingEquiv.refl F ∧ ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧
      A = Matrix.diagonal (Sum.elim ![a, b] ![a, b]) := by
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  have row : ∀ i j : Fin 2 ⊕ Fin 2, i ≠ j → A i j = 0 := by
    intro i j hij
    rcases i with k | k
    · exact (rel_facts (p := Sum.inr k) (q := Sum.inl k) σ A 1 h1 (hl k 1)).1 j (Ne.symm hij)
    · exact (rel_facts (p := Sum.inl k) (q := Sum.inr k) σ A 1 h1 (hu k 1)).1 j (Ne.symm hij)
  have hd : ∀ k : Fin 2, A (Sum.inr k) (Sum.inr k) = A (Sum.inl k) (Sum.inl k) := fun k => by
    have := (rel_facts σ A 1 h1 (hu k 1)).2.2
    rw [map_one] at this
    linear_combination -this
  have hrel : ∀ (k : Fin 2) (t : F), t ≠ 0 →
      A (Sum.inl k) (Sum.inl k) * σ t = t * A (Sum.inl k) (Sum.inl k) := fun k t ht => by
    have := (rel_facts σ A t ht (hu k t)).2.2
    rw [hd k] at this
    exact this
  have hAdiag : A = Matrix.diagonal fun i => A i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [row i j hij, Matrix.diagonal_apply_ne _ hij]
  have hprod : ∏ i, A i i ≠ 0 := by
    have := hdet
    rw [hAdiag, Matrix.det_diagonal] at this
    exact this
  have hnz : ∀ i, A i i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  refine ⟨RingEquiv.ext fun t => ?_, A (Sum.inl 0) (Sum.inl 0), A (Sum.inl 1) (Sum.inl 1),
    hnz _, hnz _, ?_⟩
  · by_cases ht : t = 0
    · rw [ht, map_zero]
      rfl
    · have := hrel 0 t ht
      have h2 : σ t = t := by
        have h3 : A (Sum.inl 0) (Sum.inl 0) * (σ t - t) = 0 := by linear_combination this
        exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left (hnz _))
      exact h2
  · ext i j
    by_cases hij : i = j
    · subst hij
      rcases i with k | k <;> fin_cases k <;> simp [hd]
    · rw [row i j hij, Matrix.diagonal_apply_ne _ hij]

theorem sp4_sq (a b μ : F) (hμ : (Matrix.diagonal (Sum.elim ![a, b] ![a, b]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 *
      Matrix.diagonal (Sum.elim ![a, b] ![a, b]) = μ • fromBlocks 0 1 (-1) 0) :
    a * a = b * b := by
  rw [Matrix.diagonal_transpose] at hμ
  have e0 := congrFun (congrFun hμ (Sum.inl 0)) (Sum.inr 0)
  have e1 := congrFun (congrFun hμ (Sum.inl 1)) (Sum.inr 1)
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul] at e0 e1
  linear_combination e0 - e1

theorem diag_sq (a b : F) (h : a * a = b * b) :
    (Matrix.diagonal (Sum.elim ![a, b] ![a, b]) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      Matrix.diagonal (Sum.elim ![a, b] ![a, b]) = (a * a) • (1 : Matrix _ _ F) := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    rcases i with k | k <;> fin_cases k <;> simp [h]
  · rw [Matrix.diagonal_apply_ne _ hij]
    simp [Matrix.one_apply_ne hij]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
