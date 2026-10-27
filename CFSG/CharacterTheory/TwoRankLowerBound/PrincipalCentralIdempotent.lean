module

public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBrauerImage

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def primitiveCentralIdempotent {ring : Type*} [CommRing ring] (element : ring) : Prop :=
  IsIdempotentElem element ∧ element ≠ 0 ∧
    ∀ other : ring, IsIdempotentElem other → other * element = other → other = 0 ∨ other = element

theorem primitive_idempotent_unique_of_hom {ring field : Type*} [CommRing ring] [CommRing field]
    [Nontrivial field] (hom : ring →+* field) {left right : ring}
    (hleft : primitiveCentralIdempotent left) (hright : primitiveCentralIdempotent right)
    (hleftValue : hom left = 1) (hrightValue : hom right = 1) : left = right := by
  have hproduct : left * right ≠ 0 := by
    intro hzero
    have hequal := congrArg hom hzero
    rw [map_mul, hleftValue, hrightValue, one_mul, map_zero] at hequal
    exact one_ne_zero hequal
  have hidempotent := hleft.1.mul hright.1
  have hleftProduct : left * right = left :=
    (hleft.2.2 (left * right) hidempotent (by rw [mul_right_comm, hleft.1.eq])).resolve_left hproduct
  have hrightProduct : left * right = right :=
    (hright.2.2 (left * right) hidempotent (by rw [mul_assoc, hright.1.eq])).resolve_left hproduct
  exact hleftProduct.symm.trans hrightProduct

theorem primitive_idempotent_map_equiv {ring : Type*} [CommRing ring]
    (equivalence : ring ≃+* ring) {element : ring} (hprimitive : primitiveCentralIdempotent element) :
    primitiveCentralIdempotent (equivalence element) := by
  refine ⟨hprimitive.1.map equivalence, ?_, ?_⟩
  · exact fun hzero => hprimitive.2.1 (equivalence.injective (hzero.trans (map_zero equivalence).symm))
  · intro other hidempotent hcorner
    have hcorner' : equivalence.symm other * element = equivalence.symm other := by
      have hequal := congrArg equivalence.symm hcorner
      simpa only [map_mul, RingEquiv.symm_apply_apply] using hequal
    rcases hprimitive.2.2 (equivalence.symm other) (hidempotent.map equivalence.symm) hcorner' with hzero | hequal
    · left
      exact equivalence.symm.injective (hzero.trans (map_zero equivalence.symm).symm)
    · right
      exact (equivalence.apply_symm_apply other).symm.trans (congrArg equivalence hequal)

theorem primitive_idempotent_fixed_of_hom {ring field : Type*} [CommRing ring] [CommRing field]
    [Nontrivial field] (equivalence : ring ≃+* ring) (hom : ring →+* field)
    (hinvariant : ∀ value, hom (equivalence value) = hom value)
    {element : ring} (hprimitive : primitiveCentralIdempotent element) (hvalue : hom element = 1) :
    equivalence element = element :=
  primitive_idempotent_unique_of_hom hom (primitive_idempotent_map_equiv equivalence hprimitive)
    hprimitive ((hinvariant element).trans hvalue) hvalue

@[expose] noncomputable def coefficientBlockIdempotent {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ) (label : basis.index) :
    centralCoefficientSubring (G := group) ring :=
  admissibleCharacterSubsetElement basis ring (coefficientBlock basis ring label)
    (coefficientBlock_admissible basis ring label)

theorem coefficientBlockIdempotent_isIdempotent {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ) (label : basis.index) :
    IsIdempotentElem (coefficientBlockIdempotent basis ring label) :=
  Subtype.ext (characterSubsetIdempotent_isIdempotent basis _).eq

theorem coefficientBlockIdempotent_primitive {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ) (label : basis.index) :
    primitiveCentralIdempotent (coefficientBlockIdempotent basis ring label) := by
  refine ⟨coefficientBlockIdempotent_isIdempotent basis ring label, ?_, ?_⟩
  · intro hzero
    have hequal := congrArg Subtype.val hzero
    change characterSubsetIdempotent basis (coefficientBlock basis ring label) = 0 at hequal
    have hsupport := (characterSubsetIdempotent_injective basis)
      (hequal.trans (characterSubsetIdempotent_empty basis).symm)
    have hmember := coefficientBlock_self_mem basis ring label
    rw [hsupport] at hmember
    exact Finset.notMem_empty label hmember
  · intro other hidempotent hcorner
    obtain ⟨support, hequal, _⟩ := central_idempotent_eq_character_subset basis other.val
      (centralCoefficientSubring_commutes ring other) (congrArg Subtype.val hidempotent.eq)
    have hadmissible : characterSubsetAdmissible basis ring support := by
      change characterSubsetIdempotent basis support ∈ groupAlgebraCoefficientSubring ring
      rw [← hequal]
      exact other.property.1
    have hsubset : support ⊆ coefficientBlock basis ring label := by
      have hequation := congrArg Subtype.val hcorner
      change other.val * characterSubsetIdempotent basis (coefficientBlock basis ring label) = other.val
        at hequation
      rw [hequal, ← characterSubsetIdempotent_inter] at hequation
      have hintersection := characterSubsetIdempotent_injective basis hequation
      exact Finset.inter_eq_left.mp hintersection
    rcases coefficientBlock_admissible_subset_empty_or_eq basis ring label support hadmissible hsubset with
      hempty | hblock
    · left
      apply Subtype.ext
      rw [hequal, hempty, characterSubsetIdempotent_empty]
      rfl
    · right
      apply Subtype.ext
      change other.val = characterSubsetIdempotent basis (coefficientBlock basis ring label)
      rw [hequal, hblock]

theorem centralCharacterResidueHom_block_idempotent {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (blockLabel label : basis.index) :
    centralCharacterResidueHom basis ideal label (coefficientBlockIdempotent basis _ blockLabel) =
      if label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel then 1 else 0 :=
  centralCharacterResidueHom_subset basis ideal _ _ label

theorem principal_block_idempotent_augmentation {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    groupAlgebraAugmentation ℂ group (coefficientBlockIdempotent basis ring principal).val = 1 := by
  have hscalar := centralComplexCharacterHom_subset basis ring _
    (coefficientBlock_admissible basis ring principal) principal
  change centralCharacterScalar basis (coefficientBlockIdempotent basis ring principal).val principal = _ at hscalar
  rw [centralCharacterScalar_principal basis principal hprincipal,
    ite_eq_left (coefficientBlock_self_mem basis ring principal)] at hscalar
  exact hscalar

end CFSG.TwoRankLowerBound.Helpers
