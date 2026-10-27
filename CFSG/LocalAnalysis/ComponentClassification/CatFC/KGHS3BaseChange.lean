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

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

theorem exists_algClosed_ringHom (F : Type) [Field F] (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ (E : Type) (_ : Field E) (_ : IsAlgClosed E) (φ : Matrix ι ι F →+* Module.End E (ι → E)),
      Function.Injective φ ∧ ringChar E = ringChar F := by
  refine ⟨AlgebraicClosure F, inferInstance, inferInstance,
    (Matrix.toLinAlgEquiv' : Matrix ι ι (AlgebraicClosure F) ≃ₐ[AlgebraicClosure F] _).toAlgHom.toRingHom.comp
      (RingHom.mapMatrix (algebraMap F (AlgebraicClosure F))), ?_, ?_⟩
  · intro A B hAB
    have h1 := Matrix.toLinAlgEquiv'.injective hAB
    exact Matrix.map_injective (algebraMap F (AlgebraicClosure F)).injective h1
  · have : CharP (AlgebraicClosure F) (ringChar F) :=
      charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective (ringChar F)
    exact ringChar.eq (AlgebraicClosure F) (ringChar F)

end CFSG.ComponentClassification.CatFC.KGHS3
