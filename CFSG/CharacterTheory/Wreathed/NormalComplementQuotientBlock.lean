module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.QuotientBlock
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

universe u

theorem normal_prime_complement_unique_quotient_principal_block {K : Type u} [Group K]
    [Fintype K] (basis : FiniteIrreducibleCharacterBasis K)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (R : Subgroup K) [R.Normal]
    [Fintype R] (hR : ¬ p ∣ Nat.card R) [Fintype (K ⧸ R)]
    (quotientBasis : FiniteIrreducibleCharacterBasis (K ⧸ R)) (quotientLabel : quotientBasis.index)
    (hone : coefficientBlock quotientBasis (localizedComplexIntegerRing ideal) quotientLabel =
      Finset.univ) :
    (∀ χ, χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      R ≤ MonoidHom.ker (basis.representation χ).representation) ∧
    (∀ χ, χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      ∃ θ : quotientBasis.index, (basis.representation χ).character =
        (quotientBasis.representation θ).character ∘ QuotientGroup.mk' R) ∧
    (∀ θ : quotientBasis.index,
      ∃ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character =
          (quotientBasis.representation θ).character ∘ QuotientGroup.mk' R) ∧
    ((Nat.card R : ℂ)⁻¹ • ∑ r : R, MonoidAlgebra.single (r : K) (1 : ℂ)) ∈
      groupAlgebraCoefficientSubring (localizedComplexIntegerRing ideal) ∧
    IsIdempotentElem ((Nat.card R : ℂ)⁻¹ • ∑ r : R, MonoidAlgebra.single (r : K) (1 : ℂ)) ∧
    (∀ x : MonoidAlgebra ℂ K,
      Commute ((Nat.card R : ℂ)⁻¹ • ∑ r : R, MonoidAlgebra.single (r : K) (1 : ℂ)) x) ∧
    characterSubsetIdempotent basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) =
      (Nat.card R : ℂ)⁻¹ • ∑ r : R, MonoidAlgebra.single (r : K) (1 : ℂ) := by
  have hblock : coefficientBlock basis (localizedComplexIntegerRing ideal) principal =
      normalSubgroupCharacterSupport basis R := by
    have hcard : ¬ p ∣ Nat.card (QuotientGroup.mk' R).ker := by
      rw [QuotientGroup.ker_mk']
      exact hR
    have e := CFSG.LyonsUnitaryFour.principal_block_eq_kernel_support_of_quotient basis
      quotientBasis ideal p (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R) hcard
      quotientLabel hone principal hprincipal
    rwa [QuotientGroup.ker_mk'] at e
  have hker : ∀ χ, χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      R ≤ MonoidHom.ker (basis.representation χ).representation := by
    intro χ
    rw [hblock]
    simp only [normalSubgroupCharacterSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h r hr => h ⟨r, hr⟩, fun h r => h r.property⟩
  have hinfl : ∀ χ (θ : quotientBasis.index), (basis.representation χ).character =
      (quotientBasis.representation θ).character ∘ QuotientGroup.mk' R →
      χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    intro χ θ hchar
    rw [hker]
    apply CFSG.LyonsUnitaryFour.le_ker_of_character_eq_degree
    intro r hr
    change (basis.representation χ).character r = (basis.representation χ).character 1
    rw [hchar]
    simp only [Function.comp_apply, map_one]
    have hr1 : (QuotientGroup.mk' R) r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    rw [hr1]
  have hiff : ∀ χ, χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      ∃ θ : quotientBasis.index, (basis.representation χ).character =
        (quotientBasis.representation θ).character ∘ QuotientGroup.mk' R := by
    intro χ
    refine ⟨fun hmem => ?_, fun ⟨θ, hθ⟩ => hinfl χ θ hθ⟩
    have hRker := (hker χ).mp hmem
    let ρ := (basis.representation χ).representation
    let ρ' : Representation ℂ (K ⧸ R) (basis.representation χ).vector :=
      QuotientGroup.lift R ρ hRker
    have hcomp : ρ'.comp (QuotientGroup.mk' R) = ρ := by
      ext g
      simp [ρ']
    let factored : FiniteComplexRepresentation.{u, u} (K ⧸ R) :=
      { vector := (basis.representation χ).vector, representation := ρ' }
    have hirr : factored.IsIrreducible := by
      apply CFSG.LyonsUnitaryFour.isIrreducible_of_comp_surjective (QuotientGroup.mk' R)
        (QuotientGroup.mk'_surjective R)
      rw [hcomp]
      exact basis.irreducible χ
    obtain ⟨θ, hθ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible quotientBasis factored
      hirr
    refine ⟨θ, ?_⟩
    rw [hθ]
    funext g
    change LinearMap.trace ℂ _ (ρ g) = LinearMap.trace ℂ _ (ρ' (QuotientGroup.mk' R g))
    rw [← MonoidHom.comp_apply, hcomp]
  have hsurj : ∀ θ : quotientBasis.index,
      ∃ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character =
          (quotientBasis.representation θ).character ∘ QuotientGroup.mk' R := by
    intro θ
    let inflated : FiniteComplexRepresentation.{u, u} K :=
      { vector := (quotientBasis.representation θ).vector
        representation := (quotientBasis.representation θ).representation.comp
          (QuotientGroup.mk' R) }
    have hirr : inflated.IsIrreducible :=
      CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective (QuotientGroup.mk' R)
        (QuotientGroup.mk'_surjective R) _ (quotientBasis.irreducible θ)
    obtain ⟨χ, hχ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis inflated hirr
    exact ⟨χ, hinfl χ θ hχ, hχ⟩
  let cardUnit : ℂˣ := Units.mk0 (Nat.card R) (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hav := normalSubgroupAverage_eq_characterSubsetIdempotent basis R cardUnit rfl
  have haR : normalSubgroupAverage R cardUnit =
      (Nat.card R : ℂ)⁻¹ • ∑ r : R, MonoidAlgebra.single (r : K) (1 : ℂ) := by
    unfold normalSubgroupAverage
    rw [Units.smul_def, Units.val_inv_eq_inv_val]
    rfl
  have heq : characterSubsetIdempotent basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) =
      (Nat.card R : ℂ)⁻¹ • ∑ r : R, MonoidAlgebra.single (r : K) (1 : ℂ) := by
    rw [hblock, ← hav, haR]
  refine ⟨hker, hiff, hsurj, ?_, ?_, ?_, heq⟩
  · rw [← heq]
    exact coefficientBlock_admissible basis _ principal
  · rw [← heq]
    exact characterSubsetIdempotent_isIdempotent basis _
  · rw [← heq]
    exact characterSubsetIdempotent_central basis _

end CFSG.Wreathed
