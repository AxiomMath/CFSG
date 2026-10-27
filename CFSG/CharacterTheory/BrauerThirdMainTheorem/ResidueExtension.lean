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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem finiteCoordinate_residue_extension (ring : Type*) [CommRing ring]
    (field : Type*) [Field field] [Algebra ring field]
    (index : Type*) [Fintype index] (subalgebra : Subalgebra ring (index → ring))
    (residue : subalgebra →ₐ[ring] field) :
    ∃ coordinate : index, ∀ value : subalgebra,
      residue value = algebraMap ring field (value.val coordinate) := by
  classical
  by_contra hnone
  have hseparating : ∀ coordinate : index, ∃ value : subalgebra,
      residue value ≠ algebraMap ring field (value.val coordinate) := by
    simpa only [not_exists, not_forall] using hnone
  choose witnesses hwitnesses using hseparating
  let factors : index → subalgebra := fun coordinate =>
    witnesses coordinate - algebraMap ring subalgebra ((witnesses coordinate).val coordinate)
  have hnonzero (coordinate : index) : residue (factors coordinate) ≠ 0 := by
    simp only [factors, map_sub, AlgHom.commutes, sub_ne_zero]
    exact hwitnesses coordinate
  have hzero : (∏ coordinate : index, factors coordinate) = 0 := by
    apply Subtype.ext
    apply funext
    intro coordinate
    change subalgebra.val (∏ entry : index, factors entry) coordinate = 0
    rw [map_prod]
    change (Pi.evalRingHom (fun _ : index => ring) coordinate)
      (∏ entry : index, subalgebra.val (factors entry)) = 0
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    change subalgebra.val (witnesses coordinate -
      algebraMap ring subalgebra ((witnesses coordinate).val coordinate)) coordinate = 0
    rw [map_sub, AlgHom.commutes]
    simp only [Pi.sub_apply, Subalgebra.val_apply, Pi.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hproduct : residue (∏ coordinate : index, factors coordinate) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun coordinate _ => hnonzero coordinate)
  rw [hzero, map_zero] at hproduct
  exact hproduct rfl

end CFSG.BrauerThirdMainTheorem.Helpers
