module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterHom

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem localCentralCharacterHom_separates {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime]
    (left right : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal))
    (hequal : ∀ label, localCentralCharacterHom basis ideal label left =
      localCentralCharacterHom basis ideal label right) : left = right := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply central_groupAlgebra_eq_zero_of_basis_actions basis
  · intro other
    exact (centralCoefficientSubring_commutes _ left other).sub_left
      (centralCoefficientSubring_commutes _ right other)
  · intro label
    rw [map_sub, centralCharacterScalar_action basis _
      (centralCoefficientSubring_commutes _ left), centralCharacterScalar_action basis _
      (centralCoefficientSubring_commutes _ right)]
    have hscalar := congrArg Subtype.val (hequal label)
    rw [localCentralCharacterHom_coe, localCentralCharacterHom_coe] at hscalar
    rw [hscalar, sub_self]

theorem finite_coordinate_prime_contains_kernel {ring coefficient index : Type*}
    [CommRing ring] [CommRing coefficient] [Fintype index]
    (coordinate : index → ring →+* coefficient)
    (hseparates : ∀ left right : ring,
      (∀ label, coordinate label left = coordinate label right) → left = right)
    (ideal : Ideal ring) [ideal.IsPrime] :
    ∃ label, RingHom.ker (coordinate label) ≤ ideal := by
  by_contra hnot
  have hexists : ∀ label, ∃ value : ring,
      value ∈ RingHom.ker (coordinate label) ∧ value ∉ ideal := by
    intro label
    exact Set.not_subset.mp (fun hle => hnot ⟨label, hle⟩)
  choose value hkernel houtside using hexists
  have hproduct : (∏ label, value label) = 0 := by
    apply hseparates
    intro label
    rw [map_prod, map_zero]
    exact Finset.prod_eq_zero (Finset.mem_univ label) (RingHom.mem_ker.mp (hkernel label))
  have hmember : (∏ label, value label) ∈ ideal := hproduct ▸ ideal.zero_mem
  obtain ⟨label, _, hinside⟩ := Ideal.IsPrime.prod_mem_iff.mp hmember
  exact houtside label hinside

theorem finite_coordinate_prime_over_scalar_kernel {ring coefficient residue index : Type*}
    [CommRing ring] [CommRing coefficient] [CommRing residue] [Fintype index]
    (coordinate : index → ring →+* coefficient) (scalar : coefficient →+* ring)
    (reduction : coefficient →+* residue)
    (hscalar : ∀ label coefficientValue, coordinate label (scalar coefficientValue) = coefficientValue)
    (hseparates : ∀ left right : ring,
      (∀ label, coordinate label left = coordinate label right) → left = right)
    (ideal : Ideal ring) [ideal.IsPrime]
    (hcontraction : Ideal.comap scalar ideal = RingHom.ker reduction) :
    ∃ label, ideal = RingHom.ker (reduction.comp (coordinate label)) := by
  obtain ⟨label, hkernel⟩ := finite_coordinate_prime_contains_kernel coordinate hseparates ideal
  refine ⟨label, ?_⟩
  ext value
  have hdifference : value - scalar (coordinate label value) ∈ ideal := by
    apply hkernel
    rw [RingHom.mem_ker, map_sub, hscalar, sub_self]
  have hmembership : value ∈ ideal ↔ scalar (coordinate label value) ∈ ideal := by
    constructor
    · intro hvalue
      have hmember := ideal.sub_mem hvalue hdifference
      simpa only [sub_sub_cancel] using hmember
    · intro hscalarMember
      have hmember := ideal.add_mem hdifference hscalarMember
      simpa only [sub_add_cancel] using hmember
  rw [hmembership]
  change coordinate label value ∈ Ideal.comap scalar ideal ↔ _
  rw [hcontraction]
  rfl

theorem centralCharacterResidueHom_prime_completeness {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (centralIdeal : Ideal (centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal)))
    [centralIdeal.IsPrime]
    (hcontraction : Ideal.comap (centralCoefficientScalarHom (localizedComplexIntegerRing ideal))
      centralIdeal = RingHom.ker (localizedComplexIntegerResidue ideal)) :
    ∃ label : basis.index, centralIdeal = RingHom.ker (centralCharacterResidueHom basis ideal label) := by
  exact finite_coordinate_prime_over_scalar_kernel
    (localCentralCharacterHom basis ideal) (centralCoefficientScalarHom _)
    (localizedComplexIntegerResidue ideal) (localCentralCharacterHom_scalar basis ideal)
    (localCentralCharacterHom_separates basis ideal) centralIdeal hcontraction

theorem scalar_surjective_residue_homs_eq_of_kernel_eq {ring coefficient residue : Type*}
    [CommRing ring] [CommRing coefficient] [CommRing residue]
    (scalar : coefficient →+* ring) (reduction : coefficient →+* residue)
    (hsurjective : Function.Surjective reduction) (left right : ring →+* residue)
    (hleft : left.comp scalar = reduction) (hright : right.comp scalar = reduction)
    (hkernel : RingHom.ker left = RingHom.ker right) : left = right := by
  apply RingHom.ext
  intro value
  obtain ⟨coefficientValue, hvalue⟩ := hsurjective (left value)
  have hleftScalar : left (scalar coefficientValue) = reduction coefficientValue :=
    RingHom.congr_fun hleft coefficientValue
  have hrightScalar : right (scalar coefficientValue) = reduction coefficientValue :=
    RingHom.congr_fun hright coefficientValue
  have hmember : value - scalar coefficientValue ∈ RingHom.ker left := by
    rw [RingHom.mem_ker, map_sub, hleftScalar, hvalue, sub_self]
  rw [hkernel, RingHom.mem_ker, map_sub, hrightScalar, hvalue, sub_eq_zero] at hmember
  exact hmember.symm

theorem centralCharacterResidueHom_completeness {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (hom : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal) →+*
      ComplexAlgebraicIntegers ⧸ ideal)
    (hscalar : hom.comp (centralCoefficientScalarHom (localizedComplexIntegerRing ideal)) =
      localizedComplexIntegerResidue ideal) :
    ∃ label : basis.index, hom = centralCharacterResidueHom basis ideal label := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  let : (RingHom.ker hom).IsPrime := RingHom.ker_isPrime hom
  have hcontraction : Ideal.comap (centralCoefficientScalarHom (localizedComplexIntegerRing ideal))
      (RingHom.ker hom) = RingHom.ker (localizedComplexIntegerResidue ideal) := by
    ext coefficient
    change hom ((centralCoefficientScalarHom _) coefficient) = 0 ↔ _
    have hequal := RingHom.congr_fun hscalar coefficient
    change hom ((centralCoefficientScalarHom _) coefficient) =
      localizedComplexIntegerResidue ideal coefficient at hequal
    rw [hequal]
    rfl
  obtain ⟨label, hkernel⟩ := centralCharacterResidueHom_prime_completeness basis ideal
    (RingHom.ker hom) hcontraction
  refine ⟨label, scalar_surjective_residue_homs_eq_of_kernel_eq (centralCoefficientScalarHom _)
    (localizedComplexIntegerResidue ideal) (localizedComplexIntegerResidue_surjective ideal)
    hom (centralCharacterResidueHom basis ideal label) hscalar ?_ hkernel⟩
  apply RingHom.ext
  exact centralCharacterResidueHom_scalar basis ideal label

end CFSG.TwoRankLowerBound.Helpers
