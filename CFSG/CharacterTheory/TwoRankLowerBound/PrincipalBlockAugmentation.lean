module

public import CFSG.CharacterTheory.TwoRankLowerBound.CoefficientBlocks
public import CFSG.CharacterTheory.TwoRankLowerBound.TwoSidedPermutation
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerPrincipalCorner

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem centralCharacterScalar_principal_augmentation {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (value : MonoidAlgebra ℂ group)
    (hcentral : ∀ other, Commute value other) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    centralCharacterScalar basis value principal = groupAlgebraAugmentation ℂ group value := by
  have haction := centralCharacterScalar_action basis value hcentral principal
  have hequal := congrArg (LinearMap.trace ℂ (basis.representation principal).vector) haction
  rw [map_smul, LinearMap.trace_one,
    ← Representation.char_one (basis.representation principal).representation] at hequal
  change LinearMap.trace ℂ (basis.representation principal).vector
    ((basis.representation principal).representation.asAlgebraHom value) =
      centralCharacterScalar basis value principal * (basis.representation principal).character 1 at hequal
  rw [hprincipal, Pi.one_apply, mul_one] at hequal
  rw [← hequal]
  conv_lhs => rw [← groupAlgebra_sum_single value]
  rw [map_sum, map_sum, groupAlgebraAugmentation_sum]
  apply Finset.sum_congr rfl
  intro element _
  rw [Representation.asAlgebraHom_single, map_smul]
  change value.coeff element * (basis.representation principal).character element = value.coeff element
  rw [hprincipal, Pi.one_apply, mul_one]

theorem characterSubsetIdempotent_principal_augmentation {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    groupAlgebraAugmentation ℂ group (characterSubsetIdempotent basis support) =
      if principal ∈ support then 1 else 0 := by
  rw [← centralCharacterScalar_principal_augmentation basis (characterSubsetIdempotent basis support)
    (characterIdempotentExpansion_central basis _) principal hprincipal]
  apply irreducible_scalar_identity_injective (basis.representation principal) (basis.irreducible principal)
  change centralCharacterScalar basis (characterSubsetIdempotent basis support) principal •
    (1 : Module.End ℂ (basis.representation principal).vector) = _
  rw [← centralCharacterScalar_action basis (characterSubsetIdempotent basis support)
    (characterIdempotentExpansion_central basis _) principal]
  exact characterIdempotentExpansion_action basis _ principal

theorem lifted_characterSubsetIdempotent_principal_augmentation {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ring : Subring ℂ) (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis ring support) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    groupAlgebraAugmentation ring group
      (liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support) hadmissible) =
      if principal ∈ support then 1 else 0 := by
  apply ring.subtype_injective
  rw [← groupAlgebraAugmentation_map,
    liftGroupAlgebraCoefficients_map ring (characterSubsetIdempotent basis support) hadmissible,
    characterSubsetIdempotent_principal_augmentation basis support principal hprincipal]
  split_ifs <;> simp

theorem lifted_characterSubsetIdempotent_subgroup_invariant {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (ring : Subring ℂ) (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis ring support) (subgroup : Subgroup group) :
    subgroupConjugationInvariant subgroup
      (liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support) hadmissible) := by
  intro element member
  apply ring.subtype_injective
  have hmap := liftGroupAlgebraCoefficients_map ring (characterSubsetIdempotent basis support) hadmissible
  have hcoeff : ∀ member : group,
      ring.subtype ((liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support)
        hadmissible).coeff member) = (characterSubsetIdempotent basis support).coeff member := by
    intro member
    have hequal := congrArg (fun value : MonoidAlgebra ℂ group => value.coeff member) hmap
    simpa only [MonoidAlgebra.coeff_mapRingHom] using hequal
  rw [hcoeff, hcoeff]
  exact central_groupAlgebra_coeff_conjugation _ (characterIdempotentExpansion_central basis _)
    member element.val

theorem principal_block_normalComplement_residue_selection {group quotientGroup : Type*}
    [Group group] [Fintype group] [Group quotientGroup] [Finite quotientGroup]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ)
    [IsLocalRing ring] (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (subgroup : Subgroup group) (hsubgroup : IsPGroup prime subgroup)
    (quotient : Subgroup.centralizer (subgroup : Set group) →* quotientGroup)
    (hsurjective : Function.Surjective quotient) (hquotient : IsPGroup prime quotientGroup)
    [Fintype quotient.ker] (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card quotient.ker)
    (support : Finset basis.index) (hadmissible : characterSubsetAdmissible basis ring support)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    MonoidAlgebra.mapRingHom (Subgroup.centralizer (subgroup : Set group)) (IsLocalRing.residue ring)
      (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group))
        (liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support) hadmissible) *
          normalSubgroupAverage quotient.ker cardUnit) =
      if principal ∈ support then
        MonoidAlgebra.mapRingHom (Subgroup.centralizer (subgroup : Set group)) (IsLocalRing.residue ring)
          (normalSubgroupAverage quotient.ker cardUnit) else 0 := by
  let lifted := liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis support) hadmissible
  have hidempotent : IsIdempotentElem lifted := by
    change lifted * lifted = lifted
    apply groupAlgebraCoefficientEmbedding_injective ring
    rw [map_mul, liftGroupAlgebraCoefficients_map ring (characterSubsetIdempotent basis support) hadmissible]
    exact (characterSubsetIdempotent_isIdempotent basis support).eq
  have hequal := residue_centralizer_normalComplement_corner (IsLocalRing.residue ring) prime subgroup
    hsubgroup quotient hsurjective hquotient cardUnit hcard lifted hidempotent
    (lifted_characterSubsetIdempotent_subgroup_invariant basis ring support hadmissible subgroup)
  rw [lifted_characterSubsetIdempotent_principal_augmentation basis ring support hadmissible
    principal hprincipal] at hequal
  split_ifs at hequal ⊢ <;> simpa only [map_one, map_zero, one_smul, zero_smul] using hequal

end CFSG.TwoRankLowerBound.Helpers
