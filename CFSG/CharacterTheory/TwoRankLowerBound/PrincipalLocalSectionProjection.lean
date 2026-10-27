module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBlockAugmentation
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerMismatchRestriction

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem normalComplement_lifted_principalBlock_eq_average {group quotientGroup : Type*}
    [Group group] [Fintype group] [Group quotientGroup] [Finite quotientGroup]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ) [IsLocalRing ring]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (quotient : group →* quotientGroup) (hsurjective : Function.Surjective quotient)
    (hquotient : IsPGroup prime quotientGroup) [Fintype quotient.ker]
    (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card quotient.ker)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    liftGroupAlgebraCoefficients ring (characterSubsetIdempotent basis (coefficientBlock basis ring principal))
      (coefficientBlock_admissible basis ring principal) = normalSubgroupAverage quotient.ker cardUnit := by
  have hblock := normalComplement_characterSupport_eq_block basis ring prime quotient hsurjective hquotient
    cardUnit hcard principal (normalSubgroupCharacterSupport_principal_mem basis quotient.ker principal hprincipal)
  apply groupAlgebraCoefficientEmbedding_injective ring
  rw [liftGroupAlgebraCoefficients_map ring
    (characterSubsetIdempotent basis (coefficientBlock basis ring principal))
      (coefficientBlock_admissible basis ring principal), normalSubgroupAverage_map_coefficients]
  have hcomplexCard : ((Units.map ring.subtype.toMonoidHom cardUnit : ℂˣ) : ℂ) = Nat.card quotient.ker := by
    change ring.subtype (cardUnit : ring) = _
    rw [hcard, map_natCast]
  rw [normalSubgroupAverage_eq_characterSubsetIdempotent basis quotient.ker _ hcomplexCard, hblock]

theorem nonprincipal_admissible_local_principal_section_zero {group quotientGroup : Type*}
    [Group group] [Fintype group] [Group quotientGroup] [Finite quotientGroup]
    (ring : Subring ℂ) [IsLocalRing ring] (prime : ℕ) [Fact prime.Prime]
    [CharP (IsLocalRing.ResidueField ring) prime]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (hadmissible : characterSubsetAdmissible basis ring support) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (hnotPrincipal : principal ∉ support)
    (primary : group) (exponent : ℕ) (hprimary : orderOf primary ∣ prime ^ exponent)
    (localBasis : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers primary : Set group)))
    (localPrincipal : localBasis.index) (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (quotient : Subgroup.centralizer (Subgroup.zpowers primary : Set group) →* quotientGroup)
    (hsurjective : Function.Surjective quotient) (hquotient : IsPGroup prime quotientGroup)
    [Fintype quotient.ker] (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card quotient.ker)
    (regular : Subgroup.centralizer (Subgroup.zpowers primary : Set group))
    (hregular : Nat.Coprime prime (orderOf regular.val))
    (hroots : ∀ period : ℕ, 0 < period → ∀ root : ℂ, root ^ period = 1 → root ∈ ring)
    (label : basis.index) (hlabel : label ∈ support) :
    characterSubsetProjection localBasis (coefficientBlock localBasis ring localPrincipal)
      (fun member => (basis.representation label).character member.val)
      ((⟨primary, element_mem_centralizer_zpowers primary⟩ :
        Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular)⁻¹ = 0 := by
  have hsubgroup : IsPGroup prime (Subgroup.zpowers primary) :=
    IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact hprimary)
  have hresidue := principal_block_normalComplement_residue_selection basis ring prime (Subgroup.zpowers primary)
    hsubgroup quotient hsurjective hquotient cardUnit hcard support hadmissible principal hprincipal
  rw [ite_eq_right hnotPrincipal] at hresidue
  rw [← normalComplement_lifted_principalBlock_eq_average localBasis ring prime quotient hsurjective
    hquotient cardUnit hcard localPrincipal hlocalPrincipal] at hresidue
  exact admissible_mismatch_character_local_projection_zero ring prime basis support hadmissible primary exponent
    hprimary localBasis (coefficientBlock localBasis ring localPrincipal)
    (coefficientBlock_admissible localBasis ring localPrincipal) regular hregular hroots hresidue label hlabel

end CFSG.TwoRankLowerBound.Helpers
