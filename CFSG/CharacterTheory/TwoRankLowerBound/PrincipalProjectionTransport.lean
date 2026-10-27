module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCoefficientTransport
public import CFSG.CharacterTheory.TwoRankLowerBound.SupportedPrincipalInduction

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem characterSubsetProjection_pairing_character {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (function : group → ℂ) (label : basis.index) :
    characterPairing (characterSubsetProjection basis support function) (basis.representation label).character =
      if label ∈ support then characterPairing function (basis.representation label).character else 0 := by
  rw [characterSubsetProjection_pairing_left]
  simp_rw [characterPairing_irreducible _ _ (basis.irreducible _) (basis.irreducible label),
    basis.distinct.eq_iff, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq' support label (fun member =>
    characterPairing function (basis.representation member).character)

theorem characterSubsetProjection_class {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (function : group → ℂ) :
    ∀ element conjugator : group,
      characterSubsetProjection basis support function (conjugator * element * conjugator⁻¹) =
        characterSubsetProjection basis support function element :=
  ((coefficientCharacterSpace_mem_iff_class_and_pairing_zero_outside basis support _).mp
    (characterSubsetProjection_mem basis support function)).1

theorem groupAlgebraClassElement_subset_projection {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (function : group → ℂ)
    (hclass : ∀ element conjugator : group,
      function (conjugator * element * conjugator⁻¹) = function element) :
    groupAlgebraClassElement (characterSubsetProjection basis support function) =
      characterSubsetIdempotent basis support * groupAlgebraClassElement function := by
  apply sub_eq_zero.mp
  apply central_groupAlgebra_eq_zero_of_basis_actions basis
  · intro other
    exact (groupAlgebraClassElement_central _ (characterSubsetProjection_class basis support function) other).sub_left
      ((characterSubsetIdempotent_central basis support other).mul_left
        (groupAlgebraClassElement_central function hclass other))
  · intro label
    rw [map_sub, map_mul, groupAlgebraClassElement_action, groupAlgebraClassElement_action,
      irreducible_weightedCharacterOperator_formula _ (basis.irreducible label) _
        (characterSubsetProjection_class basis support function),
      irreducible_weightedCharacterOperator_formula _ (basis.irreducible label) _ hclass,
      characterSubsetIdempotent, characterIdempotentExpansion_action,
      characterSubsetProjection_pairing_character]
    by_cases hlabel : label ∈ support <;> simp [hlabel]

theorem groupAlgebraClassElement_transport {source target : Type*}
    [Group source] [Fintype source] [Group target] [Fintype target]
    (equivalence : source ≃* target) (function : source → ℂ) :
    MonoidAlgebra.mapDomainRingHom ℂ equivalence.toMonoidHom (groupAlgebraClassElement function) =
      groupAlgebraClassElement (fun element => function (equivalence.symm element)) := by
  ext element
  rw [groupAlgebra_transport_coeff, groupAlgebraClassElement_coeff, groupAlgebraClassElement_coeff, map_inv]

theorem coefficientBlockIdempotent_transport {source target : Type*}
    [Group source] [Fintype source] [Group target] [Fintype target]
    (sourceBasis : FiniteIrreducibleCharacterBasis source) (targetBasis : FiniteIrreducibleCharacterBasis target)
    (ring : Subring ℂ) (equivalence : source ≃* target)
    (sourcePrincipal : sourceBasis.index) (hsourcePrincipal : (sourceBasis.representation sourcePrincipal).character = 1)
    (targetPrincipal : targetBasis.index) (htargetPrincipal : (targetBasis.representation targetPrincipal).character = 1) :
    centralCoefficientTransport ring equivalence (coefficientBlockIdempotent sourceBasis ring sourcePrincipal) =
      coefficientBlockIdempotent targetBasis ring targetPrincipal := by
  have hprimitive := coefficientBlockIdempotent_primitive sourceBasis ring sourcePrincipal
  have hinverse : ∀ value,
      centralCoefficientTransport ring equivalence (centralCoefficientTransport ring equivalence.symm value) = value := by
    intro value
    simpa only [MulEquiv.symm_symm] using centralCoefficientTransport_inverse ring equivalence.symm value
  have htransportPrimitive : primitiveCentralIdempotent
      (centralCoefficientTransport ring equivalence (coefficientBlockIdempotent sourceBasis ring sourcePrincipal)) := by
    refine ⟨hprimitive.1.map _, ?_, ?_⟩
    · intro hzero
      have hback := congrArg (centralCoefficientTransport ring equivalence.symm) hzero
      rw [centralCoefficientTransport_inverse, map_zero] at hback
      exact hprimitive.2.1 hback
    · intro other hidempotent hcorner
      have hback := congrArg (centralCoefficientTransport ring equivalence.symm) hcorner
      rw [map_mul, centralCoefficientTransport_inverse] at hback
      rcases hprimitive.2.2 (centralCoefficientTransport ring equivalence.symm other)
        (hidempotent.map _) hback with hzero | hequal
      · left
        have hforward := congrArg (centralCoefficientTransport ring equivalence) hzero
        rw [hinverse, map_zero] at hforward
        exact hforward
      · right
        have hforward := congrArg (centralCoefficientTransport ring equivalence) hequal
        rw [hinverse] at hforward
        exact hforward
  apply primitive_idempotent_unique_of_hom
    ((groupAlgebraAugmentation ℂ target).comp (centralCoefficientSubring (G := target) ring).subtype)
    htransportPrimitive (coefficientBlockIdempotent_primitive targetBasis ring targetPrincipal)
  · change groupAlgebraAugmentation ℂ target
      (centralCoefficientTransport ring equivalence (coefficientBlockIdempotent sourceBasis ring sourcePrincipal)).val = 1
    rw [centralCoefficientTransport_augmentation]
    exact principal_block_idempotent_augmentation sourceBasis ring sourcePrincipal hsourcePrincipal
  · exact principal_block_idempotent_augmentation targetBasis ring targetPrincipal htargetPrincipal

theorem principal_projection_transport {source target : Type*}
    [Group source] [Fintype source] [Group target] [Fintype target]
    (sourceBasis : FiniteIrreducibleCharacterBasis source) (targetBasis : FiniteIrreducibleCharacterBasis target)
    (ring : Subring ℂ) (equivalence : source ≃* target)
    (sourcePrincipal : sourceBasis.index) (hsourcePrincipal : (sourceBasis.representation sourcePrincipal).character = 1)
    (targetPrincipal : targetBasis.index) (htargetPrincipal : (targetBasis.representation targetPrincipal).character = 1)
    (function : source → ℂ)
    (hclass : ∀ element conjugator : source,
      function (conjugator * element * conjugator⁻¹) = function element) (element : target) :
    characterSubsetProjection targetBasis (coefficientBlock targetBasis ring targetPrincipal)
      (fun member => function (equivalence.symm member)) element =
    characterSubsetProjection sourceBasis (coefficientBlock sourceBasis ring sourcePrincipal) function
      (equivalence.symm element) := by
  have htargetClass : ∀ member conjugator : target,
      function (equivalence.symm (conjugator * member * conjugator⁻¹)) = function (equivalence.symm member) := by
    intro member conjugator
    simp only [map_mul, map_inv, hclass]
  have hidempotent := congrArg Subtype.val (coefficientBlockIdempotent_transport sourceBasis targetBasis ring
    equivalence sourcePrincipal hsourcePrincipal targetPrincipal htargetPrincipal)
  change MonoidAlgebra.mapDomainRingHom ℂ equivalence.toMonoidHom
    (characterSubsetIdempotent sourceBasis (coefficientBlock sourceBasis ring sourcePrincipal)) =
      characterSubsetIdempotent targetBasis (coefficientBlock targetBasis ring targetPrincipal) at hidempotent
  have hequal := congrArg (MonoidAlgebra.mapDomainRingHom ℂ equivalence.toMonoidHom)
    (groupAlgebraClassElement_subset_projection sourceBasis (coefficientBlock sourceBasis ring sourcePrincipal)
      function hclass)
  rw [map_mul, hidempotent, groupAlgebraClassElement_transport,
    groupAlgebraClassElement_transport, ← groupAlgebraClassElement_subset_projection targetBasis _ _ htargetClass] at hequal
  have hcoefficient := congrArg (fun value : MonoidAlgebra ℂ target => value.coeff element⁻¹) hequal
  simpa only [groupAlgebraClassElement_coeff, inv_inv, map_inv] using hcoefficient.symm

end CFSG.TwoRankLowerBound.Helpers
