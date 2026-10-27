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
public import Mathlib.RepresentationTheory.Irreducible
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

public section

namespace CFSG.LargeEvenClassification.Helpers

universe fieldUniverse groupUniverse spaceUniverse

@[expose] def linearActionRepresentation {ScalarField : Type fieldUniverse} [Field ScalarField]
    {Acting : Type groupUniverse} [Monoid Acting] {Space : Type spaceUniverse}
    [AddCommGroup Space] [Module ScalarField Space]
    (action : Acting →* (Space ≃ₗ[ScalarField] Space)) : Representation ScalarField Acting Space where
  toFun element := (action element).toLinearMap
  map_one' := by
    rw [map_one]
    rfl
  map_mul' := by
    intro first second
    rw [map_mul]
    rfl

noncomputable def irreducibleAbelianScalarAction {ScalarField : Type fieldUniverse} [Field ScalarField]
    {Acting : Type groupUniverse} [CommGroup Acting] {Space : Type spaceUniverse}
    [AddCommGroup Space] [Module ScalarField Space]
    (representation : Representation ScalarField Acting Space) :
    Acting →* ((MonoidAlgebra ScalarField Acting) ⧸
      Module.annihilator (MonoidAlgebra ScalarField Acting) representation.asModule) :=
  (Ideal.Quotient.mk _).toMonoidHom.comp (MonoidAlgebra.of ScalarField Acting)

theorem irreducibleAbelianScalarAction_ker {ScalarField : Type fieldUniverse} [Field ScalarField]
    {Acting : Type groupUniverse} [CommGroup Acting] {Space : Type spaceUniverse}
    [AddCommGroup Space] [Module ScalarField Space]
    (action : Acting →* (Space ≃ₗ[ScalarField] Space)) :
    (irreducibleAbelianScalarAction (linearActionRepresentation action)).ker = action.ker := by
  let representation := linearActionRepresentation action
  ext element
  change (Ideal.Quotient.mk (Module.annihilator (MonoidAlgebra ScalarField Acting)
    representation.asModule)) ((MonoidAlgebra.of ScalarField Acting) element) = 1 ↔ action element = 1
  rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Module.mem_annihilator]
  constructor
  · intro hkernel
    apply LinearEquiv.ext
    intro vector
    have hzero := hkernel (representation.asModuleEquiv.symm vector)
    have hzeroSpace := congrArg representation.asModuleEquiv hzero
    rw [representation.asModuleEquiv_map_smul, map_sub,
      representation.asAlgebraHom_of, map_one, map_zero,
      representation.asModuleEquiv.apply_symm_apply] at hzeroSpace
    exact sub_eq_zero.mp hzeroSpace
  · intro hkernel vector
    apply representation.asModuleEquiv.injective
    rw [representation.asModuleEquiv_map_smul, map_sub,
      representation.asAlgebraHom_of, map_one, map_zero]
    change (action element) (representation.asModuleEquiv vector) -
      representation.asModuleEquiv vector = 0
    rw [hkernel]
    simp

theorem irreducible_abelian_action_cyclic_image {ScalarField : Type fieldUniverse} [Field ScalarField]
    {Acting : Type groupUniverse} [CommGroup Acting] [Finite Acting]
    {Space : Type spaceUniverse} [AddCommGroup Space] [Module ScalarField Space]
    (action : Acting →* (Space ≃ₗ[ScalarField] Space))
    [(linearActionRepresentation action).IsIrreducible] : IsCyclic action.range := by
  let representation := linearActionRepresentation action
  let annihilator := Module.annihilator (MonoidAlgebra ScalarField Acting) representation.asModule
  let : annihilator.IsMaximal := IsSimpleModule.annihilator_isMaximal
    (R := MonoidAlgebra ScalarField Acting) (M := representation.asModule)
  let : Field ((MonoidAlgebra ScalarField Acting) ⧸ annihilator) := Ideal.Quotient.field annihilator
  let scalarAction := (irreducibleAbelianScalarAction representation).toHomUnits
  have hkernel : scalarAction.ker = action.ker := by
    rw [MonoidHom.ker_toHomUnits]
    exact irreducibleAbelianScalarAction_ker action
  let equivalence := QuotientGroup.quotientMulEquivOfEq hkernel.symm
  let embedding := ((Units.coeHom ((MonoidAlgebra ScalarField Acting) ⧸ annihilator)).comp
    (QuotientGroup.kerLift scalarAction)).comp equivalence.toMonoidHom
  have hinjective : Function.Injective embedding :=
    Units.val_injective.comp
      ((QuotientGroup.kerLift_injective scalarAction).comp equivalence.injective)
  let : IsCyclic (Acting ⧸ action.ker) := isCyclic_of_injective_ringHom embedding hinjective
  exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange action).toMonoidHom
    (QuotientGroup.quotientKerEquivRange action).surjective

end CFSG.LargeEvenClassification.Helpers
