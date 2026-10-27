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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Matrix

private lemma entry_single {K : Type*} [Field K] {m : ℕ} (h : Matrix (Fin m) (Fin m) K)
    (a b x y : Fin m) :
    (h * Matrix.single a b (1 : K) * hᵀ) x y = h x a * h y b := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.transpose_apply, Finset.sum_mul, ite_and]

private lemma entry_formula {K : Type*} [Field K] {m : ℕ} (h : Matrix (Fin m) (Fin m) K)
    (a b x y : Fin m) :
    (h * (Matrix.single a b (1 : K) - Matrix.single b a (1 : K)) * hᵀ :
      Matrix (Fin m) (Fin m) K) x y =
      h x a * h y b - h x b * h y a := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, entry_single, entry_single]

private lemma col_zero {K : Type*} [Field K] {m : ℕ} {Adj : Fin m → Fin m → Prop}
    (hirr : ∀ a, ¬ Adj a a) {h : Matrix (Fin m) (Fin m) K}
    (hfix : ∀ a b, Adj a b →
      h * (Matrix.single a b 1 - Matrix.single b a 1) * hᵀ =
        Matrix.single a b 1 - Matrix.single b a 1)
    {a b r : Fin m} (hab : Adj a b) (hra : r ≠ a) (hrb : r ≠ b) : h r a = 0 := by
  have hne : a ≠ b := by
    rintro rfl
    exact hirr _ hab
  have hA : h a a * h b b - h a b * h b a = 1 := by
    have e := congrFun (congrFun (hfix a b hab) a) b
    rw [entry_formula h a b a b] at e
    refine e.trans ?_
    simp [Matrix.single_apply, hne, hne.symm]
  have hB : h r a * h a b - h r b * h a a = 0 := by
    have e := congrFun (congrFun (hfix a b hab) r) a
    rw [entry_formula h a b r a] at e
    refine e.trans ?_
    simp [Matrix.single_apply, hra.symm, hrb.symm]
  have hC : h r a * h b b - h r b * h b a = 0 := by
    have e := congrFun (congrFun (hfix a b hab) r) b
    rw [entry_formula h a b r b] at e
    refine e.trans ?_
    simp [Matrix.single_apply, hra.symm, hne]
  linear_combination (-(h r a)) * hA - (h b a) * hB + (h a a) * hC

theorem scalar_of_fixes_edges {K : Type*} [Field K] {m : ℕ} (Adj : Fin m → Fin m → Prop)
    (hsymm : ∀ a b, Adj a b → Adj b a) (hirr : ∀ a, ¬ Adj a a)
    (htwo : ∀ a, ∃ b c, b ≠ c ∧ Adj a b ∧ Adj a c)
    (htri : ∀ a, ∃ b c, Adj a b ∧ Adj b c ∧ Adj a c)
    (hdiam : ∀ a b, a ≠ b → Adj a b ∨ ∃ c, Adj a c ∧ Adj c b)
    (h : Matrix (Fin m) (Fin m) K)
    (hfix : ∀ a b, Adj a b →
      h * (Matrix.single a b 1 - Matrix.single b a 1) * hᵀ =
        Matrix.single a b 1 - Matrix.single b a 1) :
    ∃ l : K, l ^ 2 = 1 ∧ h = l • (1 : Matrix (Fin m) (Fin m) K) := by
  have hoff : ∀ a r, r ≠ a → h r a = 0 := by
    intro a r hra
    obtain ⟨b, c, hbc, hab, hac⟩ := htwo a
    by_cases hrb : r = b
    · exact col_zero hirr hfix hac hra (fun e => hbc (hrb.symm.trans e))
    · exact col_zero hirr hfix hab hra hrb
  have hedge : ∀ a b, Adj a b → h a a * h b b = 1 := by
    intro a b hab
    have hne : a ≠ b := by
      rintro rfl
      exact hirr _ hab
    have e := congrFun (congrFun (hfix a b hab) a) b
    rw [entry_formula h a b a b] at e
    have hM : (Matrix.single a b (1 : K) - Matrix.single b a (1 : K) :
        Matrix (Fin m) (Fin m) K) a b = 1 := by
      simp [Matrix.single_apply, hne, hne.symm]
    have e' := e.trans hM
    have h1 : h a b = 0 := hoff b a hne
    linear_combination e' + (h b a) * h1
  have hsq : ∀ a, h a a ^ 2 = 1 := by
    intro a
    obtain ⟨b, c, hab, hbc, hac⟩ := htri a
    have e1 := hedge a b hab
    have e2 := hedge b c hbc
    have e3 := hedge a c hac
    linear_combination (h a a * h c c) * e1 + e3 - (h a a ^ 2) * e2
  have hEq : ∀ a b, Adj a b → h a a = h b b := by
    intro a b hab
    linear_combination (-(h a a)) * hedge a b hab + (h b b) * hsq a
  have hall : ∀ a b, h a a = h b b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · rcases hdiam a b hab with hadj | ⟨c, hac, hcb⟩
      · exact hEq a b hadj
      · exact (hEq a c hac).trans (hEq c b hcb)
  obtain ⟨l, hl2, hl⟩ : ∃ l : K, l ^ 2 = 1 ∧ ∀ a, h a a = l := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨1, by simp, fun a => a.elim0⟩
    · exact ⟨h ⟨0, hm⟩ ⟨0, hm⟩, hsq _, fun a => hall a _⟩
  refine ⟨l, hl2, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [hl]
  · rw [hoff j i hij, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]

end CFSG.ComponentClassification.CatFC.KGHS3
