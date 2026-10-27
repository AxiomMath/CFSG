module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralSubgroupProjection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def conjugacyClassSum {ring group : Type*} [CommRing ring] [Group group] [Fintype group]
    (conjugacyClass : ConjClasses group) : MonoidAlgebra ring group :=
  ∑ element : group, if ConjClasses.mk element = conjugacyClass then MonoidAlgebra.single element 1 else 0

theorem conjugacyClassSum_coeff {ring group : Type*} [CommRing ring] [Group group] [Fintype group]
    (conjugacyClass : ConjClasses group) (element : group) :
    (conjugacyClassSum (ring := ring) conjugacyClass).coeff element =
      if ConjClasses.mk element = conjugacyClass then 1 else 0 := by
  simp only [conjugacyClassSum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    apply_ite, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_zero]
  by_cases hmember : ConjClasses.mk element = conjugacyClass
  · rw [Finset.sum_eq_single element]
    · simp [hmember]
    · intro other _ hother
      split_ifs <;> simp_all
    · simp
  · rw [ite_eq_right hmember]
    apply Finset.sum_eq_zero
    intro other _
    split_ifs with hclass
    · have hequal : other ≠ element := by
        intro hequal
        exact hmember (hequal ▸ hclass)
      exact Finsupp.single_eq_of_ne (Ne.symm hequal)
    · rfl

theorem conjugacyClassSum_conjugation {ring group : Type*}
    [CommRing ring] [Group group] [Fintype group]
    (conjugacyClass : ConjClasses group) (element conjugator : group) :
    (conjugacyClassSum (ring := ring) conjugacyClass).coeff (conjugator * element * conjugator⁻¹) =
      (conjugacyClassSum (ring := ring) conjugacyClass).coeff element := by
  rw [conjugacyClassSum_coeff, conjugacyClassSum_coeff]
  have hequal : ConjClasses.mk (conjugator * element * conjugator⁻¹) = ConjClasses.mk element :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨conjugator⁻¹, by group⟩)
  rw [hequal]

@[expose] noncomputable def centralConjugacyClassSum {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (conjugacyClass : ConjClasses group) :
    centralCoefficientSubring (G := group) ring :=
  ⟨conjugacyClassSum conjugacyClass, by
    constructor
    · intro element
      rw [conjugacyClassSum_coeff]
      split_ifs
      · exact ring.one_mem
      · exact ring.zero_mem
    · apply Subring.mem_center_iff.mpr
      intro other
      exact (groupAlgebra_central_of_coeff_conjugation _
        (conjugacyClassSum_conjugation conjugacyClass) other).symm⟩

@[expose] noncomputable def conjugacyClassRepresentative {group : Type*} [Group group]
    (conjugacyClass : ConjClasses group) : group :=
  Classical.choose (ConjClasses.exists_rep conjugacyClass)

theorem conjugacyClassRepresentative_spec {group : Type*} [Group group]
    (conjugacyClass : ConjClasses group) :
    ConjClasses.mk (conjugacyClassRepresentative conjugacyClass) = conjugacyClass :=
  Classical.choose_spec (ConjClasses.exists_rep conjugacyClass)

theorem central_groupAlgebra_coeff_class {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (value : centralCoefficientSubring (G := group) ring) (element : group) :
    value.val.coeff (conjugacyClassRepresentative (ConjClasses.mk element)) = value.val.coeff element := by
  have hconjugate := ConjClasses.mk_eq_mk_iff_isConj.mp
    (conjugacyClassRepresentative_spec (ConjClasses.mk element))
  obtain ⟨conjugator, hequal⟩ := isConj_iff.mp hconjugate
  calc
    value.val.coeff (conjugacyClassRepresentative (ConjClasses.mk element)) =
        value.val.coeff
          (conjugator * conjugacyClassRepresentative (ConjClasses.mk element) * conjugator⁻¹) :=
      (central_groupAlgebra_coeff_conjugation value.val
        (centralCoefficientSubring_commutes ring value) _ _).symm
    _ = value.val.coeff element := congrArg value.val.coeff hequal

@[expose] noncomputable def centralConjugacyClassCoefficient {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (value : centralCoefficientSubring (G := group) ring)
    (conjugacyClass : ConjClasses group) : ring :=
  ⟨value.val.coeff (conjugacyClassRepresentative conjugacyClass),
    centralCoefficientSubring_coefficients ring value _⟩

theorem central_groupAlgebra_class_expansion {group : Type*} [Group group] [Fintype group]
    [Fintype (ConjClasses group)] (ring : Subring ℂ)
    (value : centralCoefficientSubring (G := group) ring) :
    value = ∑ conjugacyClass : ConjClasses group,
      centralCoefficientScalarHom ring (centralConjugacyClassCoefficient ring value conjugacyClass) *
        centralConjugacyClassSum ring conjugacyClass := by
  apply Subtype.ext
  change value.val = (centralCoefficientSubring (G := group) ring).subtype
    (∑ conjugacyClass : ConjClasses group,
      centralCoefficientScalarHom ring (centralConjugacyClassCoefficient ring value conjugacyClass) *
        centralConjugacyClassSum ring conjugacyClass)
  rw [map_sum]
  ext element
  change value.val.coeff element =
    (∑ conjugacyClass : ConjClasses group,
      (algebraMap ℂ (MonoidAlgebra ℂ group))
          (centralConjugacyClassCoefficient ring value conjugacyClass).val *
        conjugacyClassSum conjugacyClass).coeff element
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul_apply,
    conjugacyClassSum_coeff, smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  exact (central_groupAlgebra_coeff_class ring value element).symm

theorem centralCharacterResidueHom_class_expansion {group : Type*} [Group group] [Fintype group]
    [Fintype (ConjClasses group)] (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (value : centralCoefficientSubring (G := group) (localizedComplexIntegerRing ideal))
    (label : basis.index) :
    centralCharacterResidueHom basis ideal label value =
      ∑ conjugacyClass : ConjClasses group,
        localizedComplexIntegerResidue ideal (centralConjugacyClassCoefficient _ value conjugacyClass) *
          centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ conjugacyClass) := by
  conv_lhs => rw [central_groupAlgebra_class_expansion (localizedComplexIntegerRing ideal) value]
  simp only [map_sum, map_mul, centralCharacterResidueHom_scalar]

theorem centralCharacterResidueHom_eq_of_class_values {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (left right : basis.index)
    (hequal : ∀ conjugacyClass : ConjClasses group,
      centralCharacterResidueHom basis ideal left (centralConjugacyClassSum _ conjugacyClass) =
        centralCharacterResidueHom basis ideal right (centralConjugacyClassSum _ conjugacyClass)) :
    centralCharacterResidueHom basis ideal left = centralCharacterResidueHom basis ideal right := by
  let : Fintype (ConjClasses group) := Fintype.ofFinite _
  apply RingHom.ext
  intro value
  rw [centralCharacterResidueHom_class_expansion, centralCharacterResidueHom_class_expansion]
  apply Finset.sum_congr rfl
  intro conjugacyClass _
  rw [hequal]

theorem centralCharacterScalar_conjugacyClassSum_integral {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (conjugacyClass : ConjClasses group) (label : basis.index) :
    IsIntegral ℤ (centralCharacterScalar basis (conjugacyClassSum conjugacyClass) label) := by
  let ring : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  let : Algebra.IsIntegral ℤ ring := complexAlgebraicIntegers_integral
  have hintegral := centralCharacterScalar_isIntegral basis ring (conjugacyClassSum conjugacyClass)
    (centralConjugacyClassSum ring conjugacyClass).property.1
    (centralCoefficientSubring_commutes ring (centralConjugacyClassSum ring conjugacyClass)) label
  exact isIntegral_trans _ hintegral

end CFSG.TwoRankLowerBound.Helpers
