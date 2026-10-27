module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralScalarIntegrality

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def centralCoefficientSubring {G : Type*} [Group G] (ring : Subring ℂ) :
    Subring (MonoidAlgebra ℂ G) :=
  groupAlgebraCoefficientSubring ring ⊓ Subring.center (MonoidAlgebra ℂ G)

noncomputable instance centralCoefficientSubring_commRing {G : Type*} [Group G] (ring : Subring ℂ) :
    CommRing (centralCoefficientSubring (G := G) ring) :=
  { (inferInstance : Ring (centralCoefficientSubring (G := G) ring)) with
    mul_comm := by
      intro left right
      apply Subtype.ext
      change left.val * right.val = right.val * left.val
      exact (Subring.mem_center_iff.mp left.property.2 right.val).symm }

theorem centralCoefficientSubring_coefficients {G : Type*} [Group G] (ring : Subring ℂ)
    (value : centralCoefficientSubring (G := G) ring) :
    ∀ element, value.val.coeff element ∈ ring := value.property.1

theorem centralCoefficientSubring_commutes {G : Type*} [Group G] (ring : Subring ℂ)
    (value : centralCoefficientSubring (G := G) ring) :
    ∀ other : MonoidAlgebra ℂ G, Commute value.val other := by
  intro other
  exact (Subring.mem_center_iff.mp value.property.2 other).symm

@[expose] noncomputable def centralComplexCharacterHom {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ring : Subring ℂ) (label : basis.index) :
    centralCoefficientSubring (G := G) ring →+* ℂ where
  toFun value := centralCharacterScalar basis value.val label
  map_one' := by
    apply irreducible_scalar_identity_injective (basis.representation label) (basis.irreducible label)
    dsimp only
    rw [← centralCharacterScalar_action basis _
      (centralCoefficientSubring_commutes ring 1), Subring.coe_one, map_one, one_smul]
  map_mul' left right := by
    apply irreducible_scalar_identity_injective (basis.representation label) (basis.irreducible label)
    dsimp only
    rw [← centralCharacterScalar_action basis _
      (centralCoefficientSubring_commutes ring (left * right)), Subring.coe_mul, map_mul,
      centralCharacterScalar_action basis _ (centralCoefficientSubring_commutes ring left),
      centralCharacterScalar_action basis _ (centralCoefficientSubring_commutes ring right),
      smul_mul_smul_comm, one_mul]
  map_zero' := by
    apply irreducible_scalar_identity_injective (basis.representation label) (basis.irreducible label)
    dsimp only
    rw [← centralCharacterScalar_action basis _
      (centralCoefficientSubring_commutes ring 0), Subring.coe_zero, map_zero, zero_smul]
  map_add' left right := by
    apply irreducible_scalar_identity_injective (basis.representation label) (basis.irreducible label)
    dsimp only
    rw [← centralCharacterScalar_action basis _
      (centralCoefficientSubring_commutes ring (left + right)), Subring.coe_add, map_add,
      centralCharacterScalar_action basis _ (centralCoefficientSubring_commutes ring left),
      centralCharacterScalar_action basis _ (centralCoefficientSubring_commutes ring right), add_smul]

@[expose] noncomputable def centralCoefficientScalarHom {G : Type*} [Group G] (ring : Subring ℂ) :
    ring →+* centralCoefficientSubring (G := G) ring where
  toFun scalar := ⟨algebraMap ℂ (MonoidAlgebra ℂ G) scalar.val, by
    constructor
    · change ∀ element, (MonoidAlgebra.single (1 : G) scalar.val).coeff element ∈ ring
      intro element
      simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs
      · exact scalar.property
      · exact ring.zero_mem
    · apply Subring.mem_center_iff.mpr
      intro other
      exact (Algebra.commutes scalar.val other).symm⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' left right := Subtype.ext (map_mul _ left.val right.val)
  map_zero' := Subtype.ext (map_zero _)
  map_add' left right := Subtype.ext (map_add _ left.val right.val)

theorem centralComplexCharacterHom_scalar {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ring : Subring ℂ) (label : basis.index)
    (scalar : ring) :
    centralComplexCharacterHom basis ring label (centralCoefficientScalarHom ring scalar) =
      scalar.val := by
  apply irreducible_scalar_identity_injective (basis.representation label) (basis.irreducible label)
  change centralCharacterScalar basis _ label • 1 = _
  rw [← centralCharacterScalar_action basis _
    (centralCoefficientSubring_commutes ring (centralCoefficientScalarHom ring scalar))]
  change (basis.representation label).representation.asAlgebraHom
    (algebraMap ℂ (MonoidAlgebra ℂ G) scalar.val) = scalar.val • 1
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

@[expose] noncomputable def localCentralCharacterHom {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] (label : basis.index) :
    centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal) →+*
      localizedComplexIntegerRing ideal :=
  (centralComplexCharacterHom basis (localizedComplexIntegerRing ideal) label).codRestrict _
    fun value => centralCharacterScalar_mem_localizedComplexIntegerRing basis ideal
      value.val value.property.1 (centralCoefficientSubring_commutes _ value) label

theorem localCentralCharacterHom_coe {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] (label : basis.index)
    (value : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal)) :
    (localCentralCharacterHom basis ideal label value : ℂ) =
      centralCharacterScalar basis value.val label := rfl

theorem localCentralCharacterHom_scalar {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] (label : basis.index)
    (scalar : localizedComplexIntegerRing ideal) :
    localCentralCharacterHom basis ideal label
      (centralCoefficientScalarHom (localizedComplexIntegerRing ideal) scalar) = scalar := by
  apply Subtype.ext
  exact centralComplexCharacterHom_scalar basis _ label scalar

@[expose] noncomputable def centralCharacterResidueHom {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (label : basis.index) :
    centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal) →+*
      ComplexAlgebraicIntegers ⧸ ideal :=
  (localizedComplexIntegerResidue ideal).comp (localCentralCharacterHom basis ideal label)

theorem centralCharacterResidueHom_scalar {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (label : basis.index)
    (scalar : localizedComplexIntegerRing ideal) :
    centralCharacterResidueHom basis ideal label
      (centralCoefficientScalarHom (localizedComplexIntegerRing ideal) scalar) =
      localizedComplexIntegerResidue ideal scalar := by
  change localizedComplexIntegerResidue ideal
    (localCentralCharacterHom basis ideal label _) = _
  rw [localCentralCharacterHom_scalar]

theorem centralCharacterResidueHom_surjective {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (label : basis.index) :
    Function.Surjective (centralCharacterResidueHom basis ideal label) := by
  intro residue
  obtain ⟨scalar, rfl⟩ := localizedComplexIntegerResidue_surjective ideal residue
  exact ⟨centralCoefficientScalarHom _ scalar, centralCharacterResidueHom_scalar basis ideal label scalar⟩

end CFSG.TwoRankLowerBound.Helpers
