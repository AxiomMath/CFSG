module

public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianPGroupAlgebra
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterSubsetProjection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem characterSubsetIdempotent_character_convolution {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (label : basis.index) (element : group) :
    ∑ member : group, (characterSubsetIdempotent basis support).coeff member *
      (basis.representation label).character (element * member) =
      if label ∈ support then (basis.representation label).character element else 0 := by
  have haction := characterIdempotentExpansion_action basis
    (fun member => if member ∈ support then 1 else 0) label
  have hequal := congrArg
    (fun operator : Module.End ℂ (basis.representation label).vector =>
      LinearMap.trace ℂ (basis.representation label).vector
        ((basis.representation label).representation element * operator)) haction
  have hexpansion : (basis.representation label).representation.asAlgebraHom
      (characterSubsetIdempotent basis support) =
      ∑ member : group, (characterSubsetIdempotent basis support).coeff member •
        (basis.representation label).representation member := by
    conv_lhs => rw [← groupAlgebra_sum_single (characterSubsetIdempotent basis support)]
    rw [map_sum]
    simp only [Representation.asAlgebraHom_single]
  change LinearMap.trace ℂ (basis.representation label).vector
    ((basis.representation label).representation element *
      (basis.representation label).representation.asAlgebraHom (characterSubsetIdempotent basis support)) = _ at hequal
  rw [hexpansion, Finset.mul_sum, map_sum] at hequal
  simp only [mul_smul_comm, map_smul, ← map_mul (basis.representation label).representation,
    smul_eq_mul] at hequal
  simpa only [mul_one, ite_mul, one_mul, zero_mul, FiniteComplexRepresentation.character,
    Representation.character] using hequal

theorem characterSubsetProjection_convolution {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index) (function : group → ℂ)
    (hclass : ∀ element conjugator : group, function (conjugator * element * conjugator⁻¹) = function element)
    (element : group) :
    characterSubsetProjection basis support function element =
      ∑ member : group, (characterSubsetIdempotent basis support).coeff member * function (element * member) := by
  have hexpansion := finiteIrreducibleCharacterBasis_reconstruction basis function hclass
  simp_rw [hexpansion (element * _), Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsum : (∑ label, ∑ member : group,
      (characterSubsetIdempotent basis support).coeff member *
        (characterPairing function (basis.representation label).character *
          (basis.representation label).character (element * member))) =
      ∑ label, characterPairing function (basis.representation label).character *
        (if label ∈ support then (basis.representation label).character element else 0) := by
    apply Finset.sum_congr rfl
    intro label _
    calc
      _ = characterPairing function (basis.representation label).character *
          ∑ member : group, (characterSubsetIdempotent basis support).coeff member *
            (basis.representation label).character (element * member) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro member _
              ring
      _ = _ := by rw [characterSubsetIdempotent_character_convolution]
  rw [hsum]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_mem_eq]
  simp only [characterSubsetProjection, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end CFSG.TwoRankLowerBound.Helpers
