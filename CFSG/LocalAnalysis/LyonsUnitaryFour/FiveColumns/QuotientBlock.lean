module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPCentralResidueVanishing

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers

theorem coefficientBlock_eq_normalSubgroupCharacterSupport_of_quotient
    {C L : Type*} [Group C] [Fintype C] [Group L] [Fintype L]
    (basis : FiniteIrreducibleCharacterBasis C) (localBasis : FiniteIrreducibleCharacterBasis L)
    (ring : Subring ℂ) (quotient : C →* L) (hsurjective : Function.Surjective quotient)
    [Fintype quotient.ker] (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card quotient.ker)
    (localLabel : localBasis.index)
    (hone : coefficientBlock localBasis ring localLabel = Finset.univ)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    coefficientBlock basis ring principal = normalSubgroupCharacterSupport basis quotient.ker := by
  set B := coefficientBlock basis ring principal with hB
  set A := normalSubgroupCharacterSupport basis quotient.ker with hA
  have hAadm : characterSubsetAdmissible basis ring A :=
    normalSubgroupCharacterSupport_admissible basis ring quotient.ker cardUnit hcard
  have hpA : principal ∈ A :=
    normalSubgroupCharacterSupport_principal_mem basis quotient.ker principal hprincipal
  have hBA : B ⊆ A := coefficientBlock_subset_admissible basis ring A hAadm principal hpA
  set e := characterSubsetIdempotent basis B with he
  have hecentral : ∀ other, Commute e other := characterSubsetIdempotent_central basis B
  have heidem : IsIdempotentElem e := characterSubsetIdempotent_isIdempotent basis B
  have headm : ∀ g, e.coeff g ∈ ring := coefficientBlock_admissible basis ring principal
  set f := MonoidAlgebra.mapDomainRingHom ℂ quotient e with hf
  have hfcentral : ∀ other : MonoidAlgebra ℂ L, Commute f other := by
    intro other
    obtain ⟨y, rfl⟩ := groupAlgebra_mapDomain_surjective (ring := ℂ) quotient hsurjective other
    exact (hecentral y).map _
  have hfidem : IsIdempotentElem f := heidem.map _
  have hfcoeff : ∀ g, f.coeff g ∈ ring := by
    intro g
    rw [hf, groupAlgebra_quotient_coeff_sum]
    exact ring.sum_mem fun c _ => by
      split_ifs
      · exact headm c
      · exact ring.zero_mem
  obtain ⟨T, hT, -⟩ := central_idempotent_eq_character_subset localBasis f hfcentral hfidem
  have hTadm : characterSubsetAdmissible localBasis ring T := by
    change characterSubsetIdempotent localBasis T ∈ groupAlgebraCoefficientSubring ring
    rw [← hT]
    exact hfcoeff
  have hTcases := coefficientBlock_admissible_subset_empty_or_eq localBasis ring localLabel T hTadm
    (by rw [hone]; exact Finset.subset_univ T)
  let complexUnit : ℂˣ := Units.mk0 (Nat.card quotient.ker) (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hcomplex : (complexUnit : ℂ) = Nat.card quotient.ker := rfl
  have hav : normalSubgroupAverage quotient.ker complexUnit = characterSubsetIdempotent basis A :=
    normalSubgroupAverage_eq_characterSubsetIdempotent basis quotient.ker complexUnit hcomplex
  have hcorner : normalAverageQuotientSection quotient hsurjective complexUnit f = e := by
    rw [hf, normalAverageQuotientSection_mapDomain, hav, he, ← characterSubsetIdempotent_inter,
      Finset.inter_eq_right.mpr hBA]
  rcases hTcases with hTempty | hTeq
  · exfalso
    rw [hTempty, characterSubsetIdempotent_empty] at hT
    rw [hT, map_zero] at hcorner
    have hBempty : B = ∅ := characterSubsetIdempotent_injective basis
      (by rw [← he, ← hcorner, characterSubsetIdempotent_empty])
    have hpB : principal ∈ B := coefficientBlock_self_mem basis ring principal
    rw [hBempty] at hpB
    exact Finset.notMem_empty _ hpB
  · rw [hTeq, hone, characterSubsetIdempotent_univ] at hT
    have hsec : normalAverageQuotientSection quotient hsurjective complexUnit 1 =
        characterSubsetIdempotent basis A := by
      have hmap := normalAverageQuotientSection_mapDomain quotient hsurjective complexUnit
        (normalSubgroupAverage quotient.ker complexUnit)
      rw [normalSubgroupAverage_mapDomain quotient complexUnit hcomplex,
        (normalSubgroupAverage_idempotent quotient.ker complexUnit hcomplex).eq] at hmap
      rw [hmap, hav]
    rw [hT, hsec] at hcorner
    exact characterSubsetIdempotent_injective basis hcorner.symm

theorem principal_block_eq_kernel_support_of_quotient {C L : Type*} [Group C] [Fintype C]
    [Group L] [Fintype L] (basis : FiniteIrreducibleCharacterBasis C)
    (localBasis : FiniteIrreducibleCharacterBasis L) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (quotient : C →* L) (hsurjective : Function.Surjective quotient) [Fintype quotient.ker]
    (hcoprime : ¬ p ∣ Nat.card quotient.ker) (localLabel : localBasis.index)
    (hone : coefficientBlock localBasis (localizedComplexIntegerRing ideal) localLabel =
      Finset.univ)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    coefficientBlock basis (localizedComplexIntegerRing ideal) principal =
      normalSubgroupCharacterSupport basis quotient.ker := by
  have hunit : IsUnit ((Nat.card quotient.ker : ℤ) : localizedComplexIntegerRing ideal) := by
    rw [localizedComplexInteger_integer_unit_iff ideal p]
    intro hdvd
    exact hcoprime (Int.natCast_dvd_natCast.mp hdvd)
  refine coefficientBlock_eq_normalSubgroupCharacterSupport_of_quotient basis localBasis _
    quotient hsurjective hunit.unit ?_ localLabel hone principal hprincipal
  rw [IsUnit.unit_spec, Int.cast_natCast]

end CFSG.LyonsUnitaryFour
