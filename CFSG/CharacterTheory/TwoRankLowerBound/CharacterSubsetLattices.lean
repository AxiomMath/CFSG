module

public import CFSG.CharacterTheory.TwoRankLowerBound.CoefficientBlocks
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerInduction

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem coefficientCharacterSpace_pairing_zero_outside {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index)
    (function : G → ℂ) (hfunction : function ∈ coefficientCharacterSpace basis support)
    (label : basis.index) (hnot : label ∉ support) :
    characterPairing function (basis.representation label).character = 0 := by
  induction hfunction using Submodule.span_induction with
  | mem generator hmember =>
    obtain ⟨member, hmember, rfl⟩ := hmember
    rw [characterPairing_irreducible _ _ (basis.irreducible member) (basis.irreducible label)]
    have hne : (basis.representation member).character ≠ (basis.representation label).character := by
      intro hequal
      exact hnot (basis.distinct hequal ▸ hmember)
    rw [ite_eq_right hne]
  | zero => simp [characterPairing]
  | add left right _ _ hleft hright =>
    simp only [characterPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add] at hleft hright ⊢
    rw [hleft, hright, add_zero]
  | smul scalar function _ hzero =>
    have hpair := congrFun ((characterBasisComplexCoordinates basis).map_smul scalar function) label
    change characterPairing (scalar • function) (basis.representation label).character =
      scalar * characterPairing function (basis.representation label).character at hpair
    rw [hpair, hzero, mul_zero]

theorem coefficientVirtualLattice_le_virtual {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) :
    coefficientVirtualLattice basis support ≤ virtualCharacters G := by
  apply Submodule.span_le.mpr
  rintro _ ⟨label, _, rfl⟩
  exact character_mem_virtualCharacters _

theorem coefficientVirtualLattice_le_complex_space {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) :
    coefficientVirtualLattice basis support ≤ (coefficientCharacterSpace basis support).restrictScalars ℤ :=
  Submodule.span_le_restrictScalars ℤ ℂ _

theorem coefficientVirtualLattice_iff_virtual_and_complex {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) (function : G → ℂ) :
    function ∈ coefficientVirtualLattice basis support ↔
      function ∈ virtualCharacters G ∧ function ∈ coefficientCharacterSpace basis support := by
  constructor
  · intro hfunction
    exact ⟨coefficientVirtualLattice_le_virtual basis support hfunction,
      coefficientVirtualLattice_le_complex_space basis support hfunction⟩
  · rintro ⟨hvirtual, hspace⟩
    obtain ⟨coefficient, hexpansion, hpairing⟩ := virtualCharacter_basis_integer_expansion basis function hvirtual
    have houtside : ∀ label, label ∉ support → coefficient label = 0 := by
      intro label hnot
      apply Int.cast_injective (α := ℂ)
      rw [← hpairing, coefficientCharacterSpace_pairing_zero_outside basis support function hspace label hnot,
        Int.cast_zero]
    have hsum : function = ∑ label, coefficient label • (basis.representation label).character := by
      rw [← hexpansion]
      funext element
      simp only [characterBasisIntegerExpansion, LinearMap.coe_mk, AddHom.coe_mk,
        Finset.sum_apply, Pi.smul_apply]
      apply Finset.sum_congr rfl
      intro label _
      rw [zsmul_eq_mul]
    rw [hsum]
    apply Submodule.sum_mem
    intro label _
    by_cases hmember : label ∈ support
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨label, hmember, rfl⟩)
    · rw [houtside label hmember, zero_smul]
      exact (coefficientVirtualLattice basis support).zero_mem

end CFSG.TwoRankLowerBound.Helpers
