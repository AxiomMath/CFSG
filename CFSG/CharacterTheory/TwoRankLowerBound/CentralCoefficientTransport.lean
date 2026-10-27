module

public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalCentralIdempotent

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupAlgebra_transport_coeff {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) (value : MonoidAlgebra ℂ source) (element : target) :
    (MonoidAlgebra.mapDomainRingHom ℂ equivalence.toMonoidHom value).coeff element =
      value.coeff (equivalence.symm element) := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_equiv_apply value.coeff element

theorem groupAlgebra_transport_surjective {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) :
    Function.Surjective (MonoidAlgebra.mapDomainRingHom ℂ equivalence.toMonoidHom) := by
  intro value
  refine ⟨MonoidAlgebra.mapDomainRingHom ℂ equivalence.symm.toMonoidHom value, ?_⟩
  ext element
  rw [groupAlgebra_transport_coeff, groupAlgebra_transport_coeff, MulEquiv.symm_symm,
    equivalence.apply_symm_apply]

@[expose] noncomputable def centralCoefficientTransport {source target : Type*} [Group source] [Group target]
    (ring : Subring ℂ) (equivalence : source ≃* target) :
    centralCoefficientSubring (G := source) ring →+* centralCoefficientSubring (G := target) ring where
  toFun value := ⟨MonoidAlgebra.mapDomainRingHom ℂ equivalence.toMonoidHom value.val, by
    constructor
    · intro element
      rw [groupAlgebra_transport_coeff]
      exact centralCoefficientSubring_coefficients ring value _
    · apply Subring.mem_center_iff.mpr
      intro other
      obtain ⟨preimage, rfl⟩ := groupAlgebra_transport_surjective equivalence other
      exact ((centralCoefficientSubring_commutes ring value preimage).map
        (MonoidAlgebra.mapDomainRingHom ℂ equivalence.toMonoidHom)).symm⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' left right := Subtype.ext (map_add _ left.val right.val)
  map_mul' left right := Subtype.ext (map_mul _ left.val right.val)

theorem centralCoefficientTransport_coeff {source target : Type*} [Group source] [Group target]
    (ring : Subring ℂ) (equivalence : source ≃* target)
    (value : centralCoefficientSubring (G := source) ring) (element : target) :
    (centralCoefficientTransport ring equivalence value).val.coeff element =
      value.val.coeff (equivalence.symm element) :=
  groupAlgebra_transport_coeff equivalence value.val element

theorem centralCoefficientTransport_inverse {source target : Type*} [Group source] [Group target]
    (ring : Subring ℂ) (equivalence : source ≃* target)
    (value : centralCoefficientSubring (G := source) ring) :
    centralCoefficientTransport ring equivalence.symm (centralCoefficientTransport ring equivalence value) =
      value := by
  apply Subtype.ext
  ext element
  rw [centralCoefficientTransport_coeff, centralCoefficientTransport_coeff,
    MulEquiv.symm_symm, equivalence.symm_apply_apply]

noncomputable def centralCoefficientTransportEquiv {source target : Type*} [Group source] [Group target]
    (ring : Subring ℂ) (equivalence : source ≃* target) :
    centralCoefficientSubring (G := source) ring ≃+* centralCoefficientSubring (G := target) ring :=
  RingEquiv.ofRingHom (centralCoefficientTransport ring equivalence)
    (centralCoefficientTransport ring equivalence.symm)
    (by apply RingHom.ext; intro value; exact centralCoefficientTransport_inverse ring equivalence.symm value)
    (by apply RingHom.ext; intro value; exact centralCoefficientTransport_inverse ring equivalence value)

theorem centralCoefficientTransport_augmentation {source target : Type*}
    [Group source] [Fintype source] [Group target] [Fintype target]
    (ring : Subring ℂ) (equivalence : source ≃* target)
    (value : centralCoefficientSubring (G := source) ring) :
    groupAlgebraAugmentation ℂ target (centralCoefficientTransport ring equivalence value).val =
      groupAlgebraAugmentation ℂ source value.val := by
  rw [groupAlgebraAugmentation_sum, groupAlgebraAugmentation_sum]
  simp only [centralCoefficientTransport_coeff]
  exact Equiv.sum_comp equivalence.symm.toEquiv value.val.coeff

theorem principal_block_idempotent_transport_fixed {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (equivalence : group ≃* group) :
    centralCoefficientTransport ring equivalence (coefficientBlockIdempotent basis ring principal) =
      coefficientBlockIdempotent basis ring principal := by
  apply primitive_idempotent_fixed_of_hom (centralCoefficientTransportEquiv ring equivalence)
    ((groupAlgebraAugmentation ℂ group).comp (centralCoefficientSubring (G := group) ring).subtype)
  · intro value
    exact centralCoefficientTransport_augmentation ring equivalence value
  · exact coefficientBlockIdempotent_primitive basis ring principal
  · exact principal_block_idempotent_augmentation basis ring principal hprincipal

theorem centralCoefficientTransport_scalar {source target : Type*} [Group source] [Group target]
    (ring : Subring ℂ) (equivalence : source ≃* target) (scalar : ring) :
    centralCoefficientTransport ring equivalence (centralCoefficientScalarHom ring scalar) =
      centralCoefficientScalarHom ring scalar := by
  apply Subtype.ext
  change MonoidAlgebra.mapDomainRingHom ℂ equivalence.toMonoidHom (MonoidAlgebra.single 1 scalar.val) =
    MonoidAlgebra.single 1 scalar.val
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, map_one]

theorem centralCharacterResidueHom_transport_exists {source target : Type*}
    [Group source] [Fintype source] [Group target] [Fintype target]
    (sourceBasis : FiniteIrreducibleCharacterBasis source)
    (targetBasis : FiniteIrreducibleCharacterBasis target)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (equivalence : source ≃* target) (label : sourceBasis.index) :
    ∃ targetLabel : targetBasis.index, ∀ value,
      centralCharacterResidueHom targetBasis ideal targetLabel (centralCoefficientTransport _ equivalence value) =
        centralCharacterResidueHom sourceBasis ideal label value := by
  obtain ⟨targetLabel, hequal⟩ := centralCharacterResidueHom_completeness targetBasis ideal
    ((centralCharacterResidueHom sourceBasis ideal label).comp (centralCoefficientTransport _ equivalence.symm))
    (by apply RingHom.ext; intro scalar; rw [RingHom.comp_apply, RingHom.comp_apply,
          centralCoefficientTransport_scalar, centralCharacterResidueHom_scalar])
  refine ⟨targetLabel, ?_⟩
  intro value
  have hvalue := congrArg (fun hom => hom (centralCoefficientTransport _ equivalence value)) hequal
  change centralCharacterResidueHom sourceBasis ideal label
    (centralCoefficientTransport _ equivalence.symm (centralCoefficientTransport _ equivalence value)) = _ at hvalue
  rw [centralCoefficientTransport_inverse] at hvalue
  exact hvalue.symm

theorem centralCharacterResidueHom_principal_transport {source target : Type*}
    [Group source] [Fintype source] [Group target] [Fintype target]
    (sourceBasis : FiniteIrreducibleCharacterBasis source)
    (targetBasis : FiniteIrreducibleCharacterBasis target)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (equivalence : source ≃* target) (sourcePrincipal : sourceBasis.index)
    (hsourcePrincipal : (sourceBasis.representation sourcePrincipal).character = 1)
    (targetPrincipal : targetBasis.index)
    (htargetPrincipal : (targetBasis.representation targetPrincipal).character = 1)
    (value : centralCoefficientSubring (G := source) (localizedComplexIntegerRing ideal)) :
    centralCharacterResidueHom targetBasis ideal targetPrincipal (centralCoefficientTransport _ equivalence value) =
      centralCharacterResidueHom sourceBasis ideal sourcePrincipal value := by
  have hequal : localCentralCharacterHom targetBasis ideal targetPrincipal
      (centralCoefficientTransport _ equivalence value) =
        localCentralCharacterHom sourceBasis ideal sourcePrincipal value := by
    apply Subtype.ext
    rw [localCentralCharacterHom_coe, localCentralCharacterHom_coe,
      centralCharacterScalar_principal targetBasis targetPrincipal htargetPrincipal,
      centralCharacterScalar_principal sourceBasis sourcePrincipal hsourcePrincipal]
    exact centralCoefficientTransport_augmentation _ equivalence value
  exact congrArg (localizedComplexIntegerResidue ideal) hequal

end CFSG.TwoRankLowerBound.Helpers
