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
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix

variable {K F : Type} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] {r : ℕ}

@[expose] noncomputable def trForm (a : F) : LinearMap.BilinForm K F :=
  (Algebra.traceForm K F).compl₁₂ (Algebra.lmul K F a) LinearMap.id

theorem trForm_apply (a x y : F) : trForm (K := K) a x y = Algebra.trace K F (a * x * y) := by
  simp [trForm, Algebra.traceForm_apply]

@[expose] noncomputable def gram (β : Module.Basis (Fin r) K F) (a : F) : Matrix (Fin r) (Fin r) K :=
  LinearMap.BilinForm.toMatrix β (trForm a)

theorem gram_apply (β : Module.Basis (Fin r) K F) (a : F) (i j : Fin r) :
    gram β a i j = Algebra.trace K F (a * β i * β j) := by
  rw [gram, LinearMap.BilinForm.toMatrix_apply, trForm_apply]

theorem gram_transpose (β : Module.Basis (Fin r) K F) (a : F) : (gram β a)ᵀ = gram β a := by
  ext i j
  rw [transpose_apply, gram_apply, gram_apply]
  congr 1
  ring

theorem gram_add (β : Module.Basis (Fin r) K F) (a a' : F) :
    gram β (a + a') = gram β a + gram β a' := by
  ext i j
  simp only [Matrix.add_apply, gram_apply, add_mul, map_add]

theorem gram_zero (β : Module.Basis (Fin r) K F) : gram β (0 : F) = 0 := by
  ext i j
  simp [gram_apply]

theorem gram_sub (β : Module.Basis (Fin r) K F) (a a' : F) :
    gram β (a - a') = gram β a - gram β a' := by
  ext i j
  simp only [Matrix.sub_apply, gram_apply, sub_mul, map_sub]

theorem gram_conj (β : Module.Basis (Fin r) K F) (a b : F) :
    (Algebra.leftMulMatrix β b)ᵀ * gram β a * Algebra.leftMulMatrix β b = gram β (b * b * a) := by
  have h : (trForm (K := K) a).comp (Algebra.lmul K F b) (Algebra.lmul K F b) =
      trForm (b * b * a) := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [LinearMap.BilinForm.comp_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
      trForm_apply]
    congr 1
    ring
  rw [gram, gram, ← h, LinearMap.BilinForm.toMatrix_comp β β]
  rfl

theorem gram_injective (β : Module.Basis (Fin r) K F) (htr : Function.Surjective (Algebra.trace K F))
    {a a' : F} (h : gram β a = gram β a') : a = a' := by
  by_contra hne
  have hc : a - a' ≠ 0 := sub_ne_zero.2 hne
  have h0 : trForm (K := K) (a - a') = 0 := by
    apply (LinearMap.BilinForm.toMatrix β).injective
    show gram β (a - a') = 0
    rw [gram_sub, h, sub_self]
  obtain ⟨z, hz⟩ := htr 1
  have := congrArg (fun B : LinearMap.BilinForm K F => B ((a - a')⁻¹ * z) 1) h0
  simp only [trForm_apply, LinearMap.zero_apply] at this
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, hz] at this
  exact one_ne_zero this

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
