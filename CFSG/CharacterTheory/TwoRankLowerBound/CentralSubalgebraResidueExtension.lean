module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterResidueCompleteness

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem finite_coordinate_scalar_residue_extension {ring coefficient residue index : Type*}
    [CommRing ring] [CommRing coefficient] [CommRing residue] [Fintype index]
    (coordinate : index → ring →+* coefficient) (scalar : coefficient →+* ring)
    (reduction : coefficient →+* residue)
    (hscalar : ∀ label coefficientValue, coordinate label (scalar coefficientValue) = coefficientValue)
    (hseparates : ∀ left right : ring,
      (∀ label, coordinate label left = coordinate label right) → left = right)
    (subalgebra : Subring ring)
    (hcontains : ∀ coefficientValue, scalar coefficientValue ∈ subalgebra)
    (hom : subalgebra →+* residue) [IsDomain residue]
    (hhomScalar : ∀ coefficientValue,
      hom ⟨scalar coefficientValue, hcontains coefficientValue⟩ = reduction coefficientValue) :
    ∃ label, hom = (reduction.comp (coordinate label)).comp subalgebra.subtype := by
  let scalarMap : coefficient →+* subalgebra := scalar.codRestrict subalgebra hcontains
  let restricted : index → subalgebra →+* coefficient :=
    fun label => (coordinate label).comp subalgebra.subtype
  let : (RingHom.ker hom).IsPrime := RingHom.ker_isPrime hom
  have hseparatesRestricted : ∀ left right : subalgebra,
      (∀ label, restricted label left = restricted label right) → left = right := by
    intro left right hequal
    apply Subtype.ext
    exact hseparates left.val right.val hequal
  have hcontraction : Ideal.comap scalarMap (RingHom.ker hom) = RingHom.ker reduction := by
    ext coefficientValue
    change hom ⟨scalar coefficientValue, hcontains coefficientValue⟩ = 0 ↔
      reduction coefficientValue = 0
    rw [hhomScalar]
  obtain ⟨label, hkernel⟩ := finite_coordinate_prime_over_scalar_kernel restricted scalarMap reduction
    (fun label coefficientValue => hscalar label coefficientValue) hseparatesRestricted
    (RingHom.ker hom) hcontraction
  refine ⟨label, ?_⟩
  apply RingHom.ext
  intro value
  let coefficientValue := coordinate label value.val
  have hmember : value - scalarMap coefficientValue ∈ RingHom.ker
      (reduction.comp (restricted label)) := by
    rw [RingHom.mem_ker, RingHom.comp_apply, map_sub]
    change reduction (coordinate label value.val - coordinate label (scalar coefficientValue)) = 0
    rw [hscalar, sub_self, map_zero]
  rw [← hkernel, RingHom.mem_ker, map_sub] at hmember
  change hom value - hom ⟨scalar coefficientValue, hcontains coefficientValue⟩ = 0 at hmember
  rw [hhomScalar, sub_eq_zero] at hmember
  exact hmember

theorem centralSubalgebraResidue_extension {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (subalgebra : Subring (centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal)))
    (hcontains : ∀ scalar : localizedComplexIntegerRing ideal,
      centralCoefficientScalarHom (localizedComplexIntegerRing ideal) scalar ∈ subalgebra)
    (hom : subalgebra →+* ComplexAlgebraicIntegers ⧸ ideal)
    (hscalar : ∀ scalar : localizedComplexIntegerRing ideal,
      hom ⟨centralCoefficientScalarHom (localizedComplexIntegerRing ideal) scalar, hcontains scalar⟩ =
        localizedComplexIntegerResidue ideal scalar) :
    ∃ label : basis.index, hom = (centralCharacterResidueHom basis ideal label).comp subalgebra.subtype := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  exact finite_coordinate_scalar_residue_extension (localCentralCharacterHom basis ideal)
    (centralCoefficientScalarHom _) (localizedComplexIntegerResidue ideal)
    (localCentralCharacterHom_scalar basis ideal) (localCentralCharacterHom_separates basis ideal)
    subalgebra hcontains hom hscalar

end CFSG.TwoRankLowerBound.Helpers
