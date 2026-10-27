module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalAverageQuotient
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalAverageCharacterSupport
public import CFSG.CharacterTheory.TwoRankLowerBound.TwoSidedPermutation

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem normalComplement_characterSupport_eq_block {G quotientGroup : Type*}
    [Group G] [Fintype G] [Group quotientGroup] [Finite quotientGroup]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficientRing : Subring ℂ)
    [IsLocalRing coefficientRing] (prime : ℕ) [Fact prime.Prime]
    [CharP (IsLocalRing.ResidueField coefficientRing) prime]
    (quotient : G →* quotientGroup) (hsurjective : Function.Surjective quotient)
    (hgroup : IsPGroup prime quotientGroup) [Fintype quotient.ker]
    (cardUnit : coefficientRingˣ) (hcard : (cardUnit : coefficientRing) = Nat.card quotient.ker)
    (label : basis.index) (hlabel : label ∈ normalSubgroupCharacterSupport basis quotient.ker) :
    coefficientBlock basis coefficientRing label = normalSubgroupCharacterSupport basis quotient.ker := by
  let support := normalSubgroupCharacterSupport basis quotient.ker
  let blockSupport := coefficientBlock basis coefficientRing label
  have hadmissible := normalSubgroupCharacterSupport_admissible basis coefficientRing quotient.ker cardUnit hcard
  have hsubset : blockSupport ⊆ support :=
    coefficientBlock_subset_admissible basis coefficientRing support hadmissible label hlabel
  let embedding := MonoidAlgebra.mapRingHom G coefficientRing.subtype
  have hinjective : Function.Injective embedding := groupAlgebraCoefficientEmbedding_injective coefficientRing
  let average := normalSubgroupAverage quotient.ker cardUnit
  let blockElement := liftGroupAlgebraCoefficients coefficientRing (characterSubsetIdempotent basis blockSupport)
    (coefficientBlock_admissible basis coefficientRing label)
  have hblock : embedding blockElement = characterSubsetIdempotent basis blockSupport :=
    liftGroupAlgebraCoefficients_map coefficientRing _ _
  have hcomplexCard : ((Units.map coefficientRing.subtype.toMonoidHom cardUnit : ℂˣ) : ℂ) =
      Nat.card quotient.ker := by
    change coefficientRing.subtype (cardUnit : coefficientRing) = _
    rw [hcard, map_natCast]
  have haverage : embedding average = characterSubsetIdempotent basis support := by
    rw [normalSubgroupAverage_map_coefficients,
      normalSubgroupAverage_eq_characterSubsetIdempotent basis quotient.ker _ hcomplexCard]
  have hidempotent : IsIdempotentElem blockElement := by
    change blockElement * blockElement = blockElement
    apply hinjective
    rw [map_mul, hblock]
    exact (characterSubsetIdempotent_isIdempotent basis blockSupport).eq
  have hcorner : average * blockElement = blockElement := by
    apply hinjective
    rw [map_mul, haverage, hblock, ← characterSubsetIdempotent_inter,
      Finset.inter_eq_right.mpr hsubset]
  rcases normal_average_idempotent_eq_zero_or_average quotient hsurjective cardUnit hcard
    prime hgroup blockElement hidempotent hcorner with hzero | hequal
  · have hzeroComplex : characterSubsetIdempotent basis blockSupport = characterSubsetIdempotent basis ∅ := by
      rw [← hblock, hzero, map_zero, characterSubsetIdempotent_empty]
    have hempty := characterSubsetIdempotent_injective basis hzeroComplex
    have hself := coefficientBlock_self_mem basis coefficientRing label
    change label ∈ blockSupport at hself
    rw [hempty] at hself
    exact (Finset.notMem_empty label hself).elim
  · apply characterSubsetIdempotent_injective basis
    rw [← hblock, hequal, haverage]

theorem finiteIrreducibleCharacterBasis_contains_irreducible {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (data : FiniteComplexRepresentation G)
    (hirreducible : data.IsIrreducible) :
    ∃ label : basis.index, (basis.representation label).character = data.character := by
  by_contra! hnone
  have hzero : data.character = 0 := by
    apply basis.separates
    · intro element conjugator
      exact Representation.char_conj data.representation element conjugator
    · intro label
      rw [characterPairing_irreducible _ _ hirreducible (basis.irreducible label),
        ite_eq_right (Ne.symm (hnone label))]
  exact irreducible_character_degree_ne_zero data hirreducible (congrFun hzero 1)

theorem normalSubgroupCharacterSupport_principal_mem {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (subgroup : Subgroup G) [subgroup.Normal]
    [Fintype subgroup] (label : basis.index) (hprincipal : (basis.representation label).character = 1) :
    label ∈ normalSubgroupCharacterSupport basis subgroup := by
  let cardUnit : ℂˣ := Units.mk0 (Nat.card subgroup) (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hcard : (cardUnit : ℂ) = Nat.card subgroup := rfl
  have hcentral := normalSubgroupAverage_central subgroup cardUnit
  have haction := centralCharacterScalar_action basis (normalSubgroupAverage subgroup cardUnit) hcentral label
  have hscalar : centralCharacterScalar basis (normalSubgroupAverage subgroup cardUnit) label = 1 := by
    have htrace := congrArg (LinearMap.trace ℂ (basis.representation label).vector) haction
    rw [map_smul, LinearMap.trace_one,
      ← Representation.char_one (basis.representation label).representation] at htrace
    have hleft : LinearMap.trace ℂ (basis.representation label).vector
        ((basis.representation label).representation.asAlgebraHom (normalSubgroupAverage subgroup cardUnit)) = 1 := by
      unfold normalSubgroupAverage
      change LinearMap.trace ℂ (basis.representation label).vector
        ((basis.representation label).representation.asAlgebraHom
          (((cardUnit⁻¹ : ℂˣ) : ℂ) • (∑ member : subgroup,
            MonoidAlgebra.single member.val 1 : MonoidAlgebra ℂ G))) = 1
      rw [map_smul, map_sum, map_smul, map_sum]
      simp only [Representation.asAlgebraHom_single, one_smul]
      change ((cardUnit⁻¹ : ℂˣ) : ℂ) * ∑ member : subgroup,
        (basis.representation label).character member.val = 1
      rw [hprincipal]
      simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        ← Nat.card_eq_fintype_card, ← hcard, Units.inv_mul]
    rw [hleft] at htrace
    change (1 : ℂ) = centralCharacterScalar basis (normalSubgroupAverage subgroup cardUnit) label *
      (basis.representation label).character 1 at htrace
    rw [hprincipal, Pi.one_apply, mul_one] at htrace
    exact htrace.symm
  rw [hscalar, one_smul] at haction
  have hkernel := (normalSubgroupAverage_action_one_iff subgroup cardUnit hcard
    (basis.representation label)).mp haction
  simpa only [normalSubgroupCharacterSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hkernel

end CFSG.TwoRankLowerBound.Helpers
