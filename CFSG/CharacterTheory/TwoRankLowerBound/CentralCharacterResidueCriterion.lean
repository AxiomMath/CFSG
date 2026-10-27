module

public import CFSG.CharacterTheory.TwoRankLowerBound.UnitSeparatedPolynomial
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterHom

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def admissibleCharacterSubsetElement {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ring : Subring ℂ)
    (support : Finset basis.index) (hadmissible : characterSubsetAdmissible basis ring support) :
    centralCoefficientSubring (G := G) ring :=
  ⟨characterSubsetIdempotent basis support, hadmissible,
    Subring.mem_center_iff.mpr fun other => (characterSubsetIdempotent_central basis support other).symm⟩

theorem centralComplexCharacterHom_subset {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ring : Subring ℂ)
    (support : Finset basis.index) (hadmissible : characterSubsetAdmissible basis ring support)
    (label : basis.index) :
    centralComplexCharacterHom basis ring label
      (admissibleCharacterSubsetElement basis ring support hadmissible) =
      if label ∈ support then 1 else 0 := by
  apply irreducible_scalar_identity_injective (basis.representation label) (basis.irreducible label)
  dsimp only
  change centralCharacterScalar basis
    (admissibleCharacterSubsetElement basis ring support hadmissible).val label • 1 = _
  rw [← centralCharacterScalar_action basis _
    (centralCoefficientSubring_commutes ring
      (admissibleCharacterSubsetElement basis ring support hadmissible))]
  exact characterIdempotentExpansion_action basis _ label

theorem localCentralCharacterHom_subset {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime]
    (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) support)
    (label : basis.index) :
    localCentralCharacterHom basis ideal label
      (admissibleCharacterSubsetElement basis _ support hadmissible) =
      if label ∈ support then 1 else 0 := by
  apply Subtype.ext
  rw [localCentralCharacterHom_coe]
  have hequal := centralComplexCharacterHom_subset basis _ support hadmissible label
  change centralCharacterScalar basis _ label = _ at hequal
  by_cases hlabel : label ∈ support
  · simpa only [ite_eq_left hlabel, Subring.coe_one] using hequal
  · simpa only [ite_eq_right hlabel, Subring.coe_zero] using hequal

theorem centralCharacterResidueHom_subset {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) support)
    (label : basis.index) :
    centralCharacterResidueHom basis ideal label
      (admissibleCharacterSubsetElement basis _ support hadmissible) =
      if label ∈ support then 1 else 0 := by
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal label _) = _
  rw [localCentralCharacterHom_subset]
  split_ifs <;> simp

theorem unit_separated_central_character_subset_admissible {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime]
    (value : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal))
    (support : Finset basis.index)
    (hunits : ∀ left ∈ support, ∀ right ∉ support,
      IsUnit (localCentralCharacterHom basis ideal left value -
        localCentralCharacterHom basis ideal right value)) :
    characterSubsetAdmissible basis (localizedComplexIntegerRing ideal) support := by
  obtain ⟨polynomial, hevaluation⟩ := unit_separated_polynomial_projector
    (fun label => localCentralCharacterHom basis ideal label value) support hunits
  let projected := polynomial.eval₂
    (centralCoefficientScalarHom (localizedComplexIntegerRing ideal)) value
  have hscalar (label : basis.index) :
      localCentralCharacterHom basis ideal label projected =
        if label ∈ support then 1 else 0 := by
    rw [Polynomial.hom_eval₂]
    have hcomposition : (localCentralCharacterHom basis ideal label).comp
        (centralCoefficientScalarHom (localizedComplexIntegerRing ideal)) =
        RingHom.id (localizedComplexIntegerRing ideal) := by
      apply RingHom.ext
      exact localCentralCharacterHom_scalar basis ideal label
    rw [hcomposition]
    exact hevaluation label
  have hequal : projected.val = characterSubsetIdempotent basis support := by
    apply sub_eq_zero.mp
    apply central_groupAlgebra_eq_zero_of_basis_actions basis
    · intro other
      exact (centralCoefficientSubring_commutes _ projected other).sub_left
        (characterSubsetIdempotent_central basis support other)
    · intro label
      rw [map_sub, centralCharacterScalar_action basis _
        (centralCoefficientSubring_commutes _ projected), characterSubsetIdempotent,
        characterIdempotentExpansion_action]
      have hcomplex := congrArg Subtype.val (hscalar label)
      rw [localCentralCharacterHom_coe] at hcomplex
      by_cases hlabel : label ∈ support
      · simp only [ite_eq_left hlabel, Subring.coe_one] at hcomplex ⊢
        rw [hcomplex, sub_self]
      · simp only [ite_eq_right hlabel, Subring.coe_zero] at hcomplex ⊢
        rw [hcomplex, sub_self]
  change characterSubsetIdempotent basis support ∈ _
  rw [← hequal]
  exact projected.property.1

theorem centralCharacterResidueHom_fiber_admissible {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (value : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal))
    (label : basis.index) :
    characterSubsetAdmissible basis (localizedComplexIntegerRing ideal)
      (Finset.univ.filter fun other => centralCharacterResidueHom basis ideal other value =
        centralCharacterResidueHom basis ideal label value) := by
  apply unit_separated_central_character_subset_admissible basis ideal value
  intro left hleft right hright
  have hleftEqual : centralCharacterResidueHom basis ideal left value =
      centralCharacterResidueHom basis ideal label value := (Finset.mem_filter.mp hleft).2
  have hrightDifferent : centralCharacterResidueHom basis ideal right value ≠
      centralCharacterResidueHom basis ideal label value := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hright
  rw [localizedComplexIntegerResidue_isUnit_iff, map_sub, sub_ne_zero]
  change centralCharacterResidueHom basis ideal left value ≠
    centralCharacterResidueHom basis ideal right value
  exact fun hequal => hrightDifferent (hequal.symm.trans hleftEqual)

theorem sameCoefficientBlock_iff_centralCharacterResidueHom_eq {G : Type*}
    [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (left right : basis.index) :
    sameCoefficientBlock basis (localizedComplexIntegerRing ideal) left right ↔
      centralCharacterResidueHom basis ideal left = centralCharacterResidueHom basis ideal right := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  constructor
  · intro hblock
    apply RingHom.ext
    intro value
    have hmembership := hblock _ (centralCharacterResidueHom_fiber_admissible basis ideal value left)
    have hleft : left ∈ Finset.univ.filter
        (fun other => centralCharacterResidueHom basis ideal other value =
          centralCharacterResidueHom basis ideal left value) := by simp
    exact ((Finset.mem_filter.mp (hmembership.mp hleft)).2).symm
  · intro hequal support hadmissible
    have hindicator := congrArg
      (fun hom => hom (admissibleCharacterSubsetElement basis _ support hadmissible)) hequal
    rw [centralCharacterResidueHom_subset, centralCharacterResidueHom_subset] at hindicator
    by_cases hleft : left ∈ support <;> by_cases hright : right ∈ support <;>
      simp [hleft, hright] at hindicator ⊢

end CFSG.TwoRankLowerBound.Helpers
