module

public import CFSG.LinearAlgebra.FiniteSpanningAction
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

public noncomputable section

namespace CFSG.Certificates

open scoped Pointwise

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem generated_linear_le_stabilizer (X : Set V) (hX : X.Finite)
    (A : I → V ≃ₗ[K] V) (hA : ∀ i, Set.MapsTo (A i) X X) :
    Subgroup.closure (Set.range A) ≤ MulAction.stabilizer (V ≃ₗ[K] V) X := by
  apply (Subgroup.closure_le _).2
  rintro _ ⟨i, rfl⟩
  exact (MulAction.mem_stabilizer_set' hX).2 (hA i)

@[expose] def generatedLinearRestriction (X : Set V) (hX : X.Finite)
    (A : I → V ≃ₗ[K] V) (hA : ∀ i, Set.MapsTo (A i) X X) :
    Subgroup.closure (Set.range A) →* Equiv.Perm X :=
  (linearSetRestriction X).comp
    (Subgroup.inclusion (generated_linear_le_stabilizer X hX A hA))

theorem generatedLinearRestriction_range (X : Set V) (hX : X.Finite)
    (A : I → V ≃ₗ[K] V) (hA : ∀ i, Set.MapsTo (A i) X X) :
    (generatedLinearRestriction X hX A hA).range =
      Subgroup.closure (Set.range fun i =>
        generatedLinearRestriction X hX A hA
          ⟨A i, Subgroup.subset_closure ⟨i, rfl⟩⟩) := by
  let H := MulAction.stabilizer (V ≃ₗ[K] V) X
  let inc := Subgroup.inclusion (generated_linear_le_stabilizer X hX A hA)
  let B : I → H := fun i => ⟨A i, generated_linear_le_stabilizer X hX A hA
    (Subgroup.subset_closure ⟨i, rfl⟩)⟩
  have hrange : inc.range = Subgroup.closure (Set.range B) := by
    apply Subgroup.map_subtype_inj.mp
    rw [← MonoidHom.range_comp, MonoidHom.map_closure, ← Set.range_comp']
    change (Subgroup.closure (Set.range A)).subtype.range =
      Subgroup.closure (Set.range A)
    exact Subgroup.range_subtype _
  change ((linearSetRestriction X).comp inc).range = _
  rw [MonoidHom.range_comp, hrange, MonoidHom.map_closure, ← Set.range_comp']
  rfl

theorem invariant_spanning_linear_action (X : Set V) (hX : X.Finite)
    (hspan : Submodule.span K X = ⊤) (A : I → V ≃ₗ[K] V)
    (hA : ∀ i, Set.MapsTo (A i) X X) :
    ∃ ρ : Subgroup.closure (Set.range A) →* Equiv.Perm X,
      (∀ (g : Subgroup.closure (Set.range A)) (x : X),
        ((ρ g) x : V) = (g : V ≃ₗ[K] V) (x : V)) ∧
      Function.Injective ρ ∧
      ρ.range = Subgroup.closure (Set.range fun i =>
        ρ ⟨A i, Subgroup.subset_closure ⟨i, rfl⟩⟩) := by
  refine ⟨generatedLinearRestriction X hX A hA, fun _ _ => rfl, ?_,
    generatedLinearRestriction_range X hX A hA⟩
  exact (linearSetRestriction_injective X hspan).comp
    (Subgroup.inclusion_injective (generated_linear_le_stabilizer X hX A hA))

end CFSG.Certificates
