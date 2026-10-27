module

public import CFSG.CharacterTheory.TwoRankLowerBound.ExtendedBrauerSpanning
public import CFSG.CharacterTheory.TwoRankLowerBound.IntegralLatticeDescent

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def characterBasisIntegerExpansion {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) : (basis.index → ℤ) →ₗ[ℤ] (G → ℂ) where
  toFun := fun coefficient element => ∑ label, (coefficient label : ℂ) * (basis.representation label).character element
  map_add' := by
    intro left right
    funext element
    simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar coefficient
    funext element
    simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro label _
    ring

theorem characterBasisIntegerExpansion_virtual {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficient : basis.index → ℤ) :
    characterBasisIntegerExpansion basis coefficient ∈ virtualCharacters G := by
  have hequal : characterBasisIntegerExpansion basis coefficient =
      ∑ label, coefficient label • (basis.representation label).character := by
    funext element
    change (∑ label, (coefficient label : ℂ) * (basis.representation label).character element) = _
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro label _
    change (coefficient label : ℂ) * (basis.representation label).character element =
      coefficient label • (basis.representation label).character element
    rw [zsmul_eq_mul]
  rw [hequal]
  apply Submodule.sum_mem
  intro label _
  exact Submodule.smul_mem _ _ (character_mem_virtualCharacters _)

theorem virtualCharacter_basis_integer_expansion {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (function : G → ℂ)
    (hvirtual : function ∈ virtualCharacters G) :
    ∃ coefficient : basis.index → ℤ, characterBasisIntegerExpansion basis coefficient = function ∧
      ∀ label, characterPairing function (basis.representation label).character = coefficient label := by
  choose coefficient hcoefficient using (fun label => characterPairing_virtual_irreducible_integer
    function hvirtual (basis.representation label) (basis.irreducible label))
  refine ⟨coefficient, ?_, hcoefficient⟩
  funext element
  have hequal := finiteIrreducibleCharacterBasis_reconstruction basis function
    (virtualCharacter_conjugation_invariant function hvirtual) element
  simp only [hcoefficient] at hequal
  exact hequal.symm

@[expose] noncomputable def characterBasisComplexCoordinates {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) : (G → ℂ) →ₗ[ℂ] (basis.index → ℂ) where
  toFun := fun function label => characterPairing function (basis.representation label).character
  map_add' := by
    intro left right
    funext label
    simp only [characterPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' := by
    intro scalar function
    funext label
    simp only [characterPairing, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    rw [← Finset.mul_sum]
    ring

theorem characterBasisComplexCoordinates_integer_expansion {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (coefficient : basis.index → ℤ) :
    characterBasisComplexCoordinates basis (characterBasisIntegerExpansion basis coefficient) =
      fun label => (coefficient label : ℂ) := by
  funext label
  exact characterPairing_distinct_expansion_coefficient basis.representation basis.irreducible basis.distinct
    (fun label => (coefficient label : ℂ)) label

theorem elementary_coordinates_algebraic_span {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (function : G → ℂ)
    (hspan : function ∈ extendedElementaryInductionSpan G) :
    characterBasisComplexCoordinates basis function ∈ Submodule.span ComplexAlgebraicIntegers
      {values : basis.index → ℂ | ∃ integerValues :
        (elementaryInductionLattice G).comap (characterBasisIntegerExpansion basis),
        values = fun coordinate => ((integerValues : basis.index → ℤ) coordinate : ℂ)} := by
  induction hspan using Submodule.span_induction with
  | mem generator hmember =>
    obtain ⟨coefficient, hexpansion, hcoefficient⟩ := virtualCharacter_basis_integer_expansion basis generator
      (elementaryInductionLattice_le_virtual hmember)
    apply Submodule.subset_span
    refine ⟨⟨coefficient, ?_⟩, ?_⟩
    · change characterBasisIntegerExpansion basis coefficient ∈ elementaryInductionLattice G
      rw [hexpansion]
      exact hmember
    · funext coordinate
      exact hcoefficient coordinate
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add left right _ _ hleft hright =>
    rw [map_add]
    exact Submodule.add_mem _ hleft hright
  | smul scalar function _ hmember =>
    rw [show characterBasisComplexCoordinates basis (scalar • function) =
      scalar • characterBasisComplexCoordinates basis function from
        ((characterBasisComplexCoordinates basis).restrictScalars ComplexAlgebraicIntegers).map_smul _ _]
    exact Submodule.smul_mem _ scalar hmember

theorem elementaryInductionLattice_eq_virtual {G : Type*} [Group G] [Fintype G] :
    elementaryInductionLattice G = virtualCharacters G := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  let lattice := (elementaryInductionLattice G).comap (characterBasisIntegerExpansion basis)
  have htop : lattice = ⊤ := by
    apply integer_lattice_eq_top_of_algebraic_span lattice
    intro coefficient
    have hvirtual := characterBasisIntegerExpansion_virtual basis coefficient
    have hspan : characterBasisIntegerExpansion basis coefficient ∈ extendedElementaryInductionSpan G := by
      rw [extendedElementaryInductionSpan_eq_characterSpan]
      exact Submodule.subset_span hvirtual
    have hcoordinates := elementary_coordinates_algebraic_span basis _ hspan
    rw [characterBasisComplexCoordinates_integer_expansion] at hcoordinates
    exact hcoordinates
  apply le_antisymm elementaryInductionLattice_le_virtual
  intro function hvirtual
  obtain ⟨coefficient, hexpansion, _⟩ := virtualCharacter_basis_integer_expansion basis function hvirtual
  have hmember : coefficient ∈ lattice := by rw [htop]; trivial
  change characterBasisIntegerExpansion basis coefficient ∈ elementaryInductionLattice G at hmember
  rw [hexpansion] at hmember
  exact hmember

end CFSG.TwoRankLowerBound.Helpers
