module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerInduction

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem characterPairing_elementary_lattice_integer {G : Type*} [Group G] [Fintype G]
    (function : G → ℂ)
    (hclass : ∀ element conjugator : G, function (conjugator * element * conjugator⁻¹) = function element)
    (hrestrictions : ∀ subgroup : Subgroup G, BrauerElementary subgroup →
      function ∘ subgroup.subtype ∈ virtualCharacters subgroup)
    (character : G → ℂ) (hcharacter : character ∈ elementaryInductionLattice G) :
    ∃ integer : ℤ, characterPairing function character = integer := by
  induction hcharacter using Submodule.span_induction with
  | mem generator hmember =>
    obtain ⟨subgroup, helementary, localFunction, hvirtual, rfl⟩ := hmember
    rw [characterPairing_inducedFunction_right subgroup localFunction function hclass]
    exact characterPairing_virtual_integer _ localFunction (hrestrictions subgroup helementary) hvirtual
  | zero => exact ⟨0, by simp [characterPairing]⟩
  | add left right _ _ hleft hright =>
    obtain ⟨leftInteger, hleftValue⟩ := hleft
    obtain ⟨rightInteger, hrightValue⟩ := hright
    refine ⟨leftInteger + rightInteger, ?_⟩
    simp only [characterPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib, mul_add] at hleftValue hrightValue ⊢
    rw [hleftValue, hrightValue, Int.cast_add]
  | smul scalar character _ hinteger =>
    obtain ⟨integer, hvalue⟩ := hinteger
    refine ⟨scalar * integer, ?_⟩
    have hequal : characterPairing function (scalar • character) = (scalar : ℂ) * characterPairing function character := by
      simp only [characterPairing, Pi.smul_apply, zsmul_eq_mul]
      simp_rw [mul_left_comm (function _) (scalar : ℂ)]
      rw [← Finset.mul_sum]
      ring
    rw [hequal, hvalue, Int.cast_mul]

theorem brauer_virtual_character_criterion {G : Type*} [Group G] [Fintype G]
    (function : G → ℂ)
    (hclass : ∀ element conjugator : G, function (conjugator * element * conjugator⁻¹) = function element) :
    function ∈ virtualCharacters G ↔ ∀ subgroup : Subgroup G, BrauerElementary subgroup →
      function ∘ subgroup.subtype ∈ virtualCharacters subgroup := by
  constructor
  · intro hvirtual subgroup _
    exact inflation_mem_virtualCharacters subgroup.subtype hvirtual
  · intro hrestrictions
    obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
    apply (virtualCharacter_iff_integer_basis_pairings basis function hclass).mpr
    intro label
    apply characterPairing_elementary_lattice_integer function hclass hrestrictions
    rw [elementaryInductionLattice_eq_virtual]
    exact character_mem_virtualCharacters _

end CFSG.TwoRankLowerBound.Helpers
