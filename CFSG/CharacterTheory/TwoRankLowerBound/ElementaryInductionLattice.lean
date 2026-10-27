module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterIntegralCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicCharacterRing
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerElementary

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def elementaryInductionLattice (G : Type*) [Group G] [Fintype G] : Submodule ℤ (G → ℂ) :=
  Submodule.span ℤ {function | ∃ subgroup : Subgroup G, BrauerElementary subgroup ∧
    ∃ localFunction : subgroup → ℂ, localFunction ∈ virtualCharacters subgroup ∧
      inducedFunction subgroup localFunction = function}

theorem elementaryInductionLattice_le_virtual {G : Type*} [Group G] [Fintype G] :
    elementaryInductionLattice G ≤ virtualCharacters G := by
  apply Submodule.span_le.mpr
  rintro function ⟨subgroup, _, localFunction, hvirtual, rfl⟩
  exact inducedFunction_mem_virtualCharacters subgroup hvirtual

theorem virtual_mul_elementaryInductionLattice {G : Type*} [Group G] [Fintype G]
    (character function : G → ℂ) (hcharacter : character ∈ virtualCharacters G)
    (hfunction : function ∈ elementaryInductionLattice G) :
    character * function ∈ elementaryInductionLattice G := by
  induction hfunction using Submodule.span_induction with
  | mem generator hmember =>
    obtain ⟨subgroup, helementary, localFunction, hlocalVirtual, rfl⟩ := hmember
    rw [inducedFunction_projection_formula subgroup localFunction character
      (virtualCharacter_conjugation_invariant character hcharacter)]
    apply Submodule.subset_span
    refine ⟨subgroup, helementary, _, ?_, rfl⟩
    exact virtualCharacters_mul (character ∘ subgroup.subtype) localFunction
      (inflation_mem_virtualCharacters _ hcharacter) hlocalVirtual
  | zero => simpa only [mul_zero] using (elementaryInductionLattice G).zero_mem
  | add left right _ _ hleft hright =>
    rw [mul_add]
    exact (elementaryInductionLattice G).add_mem hleft hright
  | smul scalar function _ hmember =>
    rw [mul_smul_comm]
    exact (elementaryInductionLattice G).smul_mem scalar hmember

@[expose] def extendedElementaryInductionSpan (G : Type*) [Group G] [Fintype G] :
    Submodule ComplexAlgebraicIntegers (G → ℂ) :=
  Submodule.span ComplexAlgebraicIntegers (elementaryInductionLattice G : Set (G → ℂ))

theorem extendedElementaryInductionSpan_le_characterSpan {G : Type*} [Group G] [Fintype G] :
    extendedElementaryInductionSpan G ≤ algebraicCharacterSpan G :=
  Submodule.span_mono elementaryInductionLattice_le_virtual

theorem algebraicCharacterSpan_mul_extendedElementary {G : Type*} [Group G] [Fintype G]
    (character function : G → ℂ) (hcharacter : character ∈ algebraicCharacterSpan G)
    (hfunction : function ∈ extendedElementaryInductionSpan G) :
    character * function ∈ extendedElementaryInductionSpan G := by
  induction hcharacter using Submodule.span_induction with
  | mem generator hvirtual =>
    induction hfunction using Submodule.span_induction with
    | mem other hother => exact Submodule.subset_span (virtual_mul_elementaryInductionLattice _ _ hvirtual hother)
    | zero => simpa only [mul_zero] using (extendedElementaryInductionSpan G).zero_mem
    | add left right _ _ hleft hright =>
      rw [mul_add]
      exact (extendedElementaryInductionSpan G).add_mem hleft hright
    | smul scalar function _ hmember =>
      rw [mul_smul_comm]
      exact (extendedElementaryInductionSpan G).smul_mem scalar hmember
  | zero => simpa only [zero_mul] using (extendedElementaryInductionSpan G).zero_mem
  | add left right _ _ hleft hright =>
    rw [add_mul]
    exact (extendedElementaryInductionSpan G).add_mem hleft hright
  | smul scalar character _ hmember =>
    rw [smul_mul_assoc]
    exact (extendedElementaryInductionSpan G).smul_mem scalar hmember

@[expose] def elementaryInductionIdeal (G : Type*) [Group G] [Fintype G] : Ideal (algebraicCharacterRing G) where
  carrier := {function | (fun element => ((function : G → ComplexAlgebraicIntegers) element : ℂ)) ∈
    extendedElementaryInductionSpan G}
  zero_mem' := (extendedElementaryInductionSpan G).zero_mem
  add_mem' := by
    intro left right hleft hright
    exact (extendedElementaryInductionSpan G).add_mem hleft hright
  smul_mem' := by
    intro character function hfunction
    exact algebraicCharacterSpan_mul_extendedElementary _ _ character.property hfunction

@[expose] noncomputable def inducedFunctionComplexLinearMap {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) : (subgroup → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := inducedFunction subgroup
  map_add' := (inducedFunctionLinearMap subgroup).map_add
  map_smul' := by
    intro scalar function
    funext element
    simp only [inducedFunction, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hsum : (∑ conjugator : G, if hmember : conjugator⁻¹ * element * conjugator ∈ subgroup then
        scalar * function ⟨conjugator⁻¹ * element * conjugator, hmember⟩ else 0) =
        scalar * ∑ conjugator : G, if hmember : conjugator⁻¹ * element * conjugator ∈ subgroup then
          function ⟨conjugator⁻¹ * element * conjugator, hmember⟩ else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro conjugator _
      split_ifs <;> simp
    rw [hsum]
    ring

theorem extended_elementary_induction_mem {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (helementary : BrauerElementary subgroup)
    (function : subgroup → ℂ) (hmember : function ∈ algebraicCharacterSpan subgroup) :
    inducedFunction subgroup function ∈ extendedElementaryInductionSpan G := by
  have hmap : algebraicCharacterSpan subgroup ≤ (extendedElementaryInductionSpan G).comap
      ((inducedFunctionComplexLinearMap subgroup).restrictScalars ComplexAlgebraicIntegers) := by
    apply Submodule.span_le.mpr
    intro localFunction hvirtual
    apply Submodule.subset_span
    exact Submodule.subset_span ⟨subgroup, helementary, localFunction, hvirtual, rfl⟩
  exact hmap hmember

end CFSG.TwoRankLowerBound.Helpers
