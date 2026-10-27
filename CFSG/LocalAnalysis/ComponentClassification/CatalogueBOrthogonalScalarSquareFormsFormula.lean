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

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

universe u v w

variable {K : Type u} {E : Type v} {V : Type w}
  [Field K] [Field E] [Algebra K E] [AddCommGroup V] [Module K V]

@[expose] def positiveFormula (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (x y : V) : E :=
  algebraMap K E (B x y) + algebraMap K E (d⁻¹ * B (T x) y) * s

@[expose] def negativeFormula (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (x y : V) : E :=
  algebraMap K E (B x y) + algebraMap K E (d⁻¹ * B x (T y)) * s

theorem positiveFormula_add_left (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (x x' y : V) :
    positiveFormula B T d s (x + x') y =
      positiveFormula B T d s x y + positiveFormula B T d s x' y := by
  simp only [positiveFormula, map_add, LinearMap.add_apply, mul_add, add_mul]
  ring

theorem positiveFormula_add_right (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (x y y' : V) :
    positiveFormula B T d s x (y + y') =
      positiveFormula B T d s x y + positiveFormula B T d s x y' := by
  simp only [positiveFormula, map_add, mul_add, add_mul]
  ring

theorem negativeFormula_add_left (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (x x' y : V) :
    negativeFormula B T d s (x + x') y =
      negativeFormula B T d s x y + negativeFormula B T d s x' y := by
  simp only [negativeFormula, map_add, LinearMap.add_apply, mul_add, add_mul]
  ring

theorem negativeFormula_add_right (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (x y y' : V) :
    negativeFormula B T d s x (y + y') =
      negativeFormula B T d s x y + negativeFormula B T d s x y' := by
  simp only [negativeFormula, map_add, mul_add, add_mul]
  ring

theorem positiveFormula_smul_left (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (a : K) (x y : V) :
    positiveFormula B T d s (a • x) y =
      algebraMap K E a * positiveFormula B T d s x y := by
  simp only [positiveFormula, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
  ring

theorem positiveFormula_smul_right (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (a : K) (x y : V) :
    positiveFormula B T d s x (a • y) =
      algebraMap K E a * positiveFormula B T d s x y := by
  simp only [positiveFormula, map_smul, smul_eq_mul, map_mul]
  ring

theorem negativeFormula_smul_left (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (a : K) (x y : V) :
    negativeFormula B T d s (a • x) y =
      algebraMap K E a * negativeFormula B T d s x y := by
  simp only [negativeFormula, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
  ring

theorem negativeFormula_smul_right (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (a : K) (x y : V) :
    negativeFormula B T d s x (a • y) =
      algebraMap K E a * negativeFormula B T d s x y := by
  simp only [negativeFormula, map_smul, smul_eq_mul, map_mul]
  ring

private theorem inverse_coefficient (d : K) (hd : d ≠ 0) (a : K) :
    d⁻¹ * (d * a) = a := by rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]

theorem positiveFormula_operator_left (B : LinearMap.BilinForm K V)
    (T : Module.End K V) (d : K) (s : E) (hd : d ≠ 0)
    (hs : s ^ 2 = algebraMap K E d) (hT : ∀ x, T (T x) = d • x) (x y : V) :
    positiveFormula B T d s (T x) y = s * positiveFormula B T d s x y := by
  have hi : algebraMap K E d⁻¹ * algebraMap K E d = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hd, map_one]
  simp only [positiveFormula, hT, map_smul, LinearMap.smul_apply, smul_eq_mul,
    inverse_coefficient d hd]
  simp only [map_mul]
  linear_combination
    -(algebraMap K E d⁻¹ * algebraMap K E (B (T x) y)) * hs +
    -(algebraMap K E (B (T x) y)) * hi

theorem positiveFormula_operator_right (B : LinearMap.BilinForm K V)
    (T : Module.End K V) (d : K) (s : E) (hd : d ≠ 0)
    (hs : s ^ 2 = algebraMap K E d) (hT : ∀ x, T (T x) = d • x)
    (hadj : ∀ x y, B (T x) y = B x (T y)) (x y : V) :
    positiveFormula B T d s x (T y) = s * positiveFormula B T d s x y := by
  have he : positiveFormula B T d s x (T y) = positiveFormula B T d s (T x) y := by
    simp only [positiveFormula, ← hadj, hT, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
  rw [he, positiveFormula_operator_left B T d s hd hs hT]

theorem positiveFormula_symm (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (hB : B.IsSymm)
    (hadj : ∀ x y, B (T x) y = B x (T y)) (x y : V) :
    positiveFormula B T d s y x = positiveFormula B T d s x y := by
  rw [positiveFormula, positiveFormula, hB.eq y x, hadj, hB.eq y (T x)]

theorem negativeFormula_operator_left (B : LinearMap.BilinForm K V)
    (T : Module.End K V) (d : K) (s : E) (hd : d ≠ 0)
    (hs : s ^ 2 = algebraMap K E d) (hT : ∀ x, T (T x) = d • x)
    (hadj : ∀ x y, B (T x) y = -B x (T y)) (x y : V) :
    negativeFormula B T d s (T x) y = -s * negativeFormula B T d s x y := by
  have hi : algebraMap K E d⁻¹ * algebraMap K E d = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hd, map_one]
  simp only [negativeFormula, hadj, hT, map_smul, smul_eq_mul, map_mul, map_neg]
  linear_combination
    (algebraMap K E d⁻¹ * algebraMap K E (B x (T y))) * hs -
    -(algebraMap K E (B x (T y)) - algebraMap K E (B x y) * s) * hi

theorem negativeFormula_operator_right (B : LinearMap.BilinForm K V)
    (T : Module.End K V) (d : K) (s : E) (hd : d ≠ 0)
    (hs : s ^ 2 = algebraMap K E d) (hT : ∀ x, T (T x) = d • x) (x y : V) :
    negativeFormula B T d s x (T y) = s * negativeFormula B T d s x y := by
  have hi : algebraMap K E d⁻¹ * algebraMap K E d = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hd, map_one]
  simp only [negativeFormula, hT, map_smul, smul_eq_mul, inverse_coefficient d hd]
  simp only [map_mul]
  linear_combination
    -(algebraMap K E d⁻¹ * algebraMap K E (B x (T y))) * hs +
    -(algebraMap K E (B x (T y))) * hi

theorem negativeFormula_hermitian (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (d : K) (s : E) (bar : E ≃ₐ[K] E) (hbar : bar s = -s) (hB : B.IsSymm)
    (hadj : ∀ x y, B (T x) y = -B x (T y)) (x y : V) :
    negativeFormula B T d s y x = bar (negativeFormula B T d s x y) := by
  simp only [negativeFormula, map_add, map_mul, AlgEquiv.commutes, hbar]
  rw [hB.eq y x, hB.eq y (T x), hadj]
  simp only [mul_neg, map_neg, neg_mul]

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
