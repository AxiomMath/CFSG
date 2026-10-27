module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterInflation
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterParity
public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicIntegerResidue

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem irreducible_central_character_root_value {G : Type*} [Group G] [Finite G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (element : G) (hcentral : element ∈ Subgroup.center G) :
    ∃ scalar : ℂ, scalar ^ orderOf element = 1 ∧
      data.character element = scalar * data.character 1 := by
  let : data.representation.IsIrreducible := hirreducible
  obtain ⟨scalar, hscalar⟩ := irreducible_central_element_is_scalar data.representation element hcentral
  let : Nontrivial data.representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) data.representation.asModule
  let : Nontrivial data.vector := data.representation.asModuleEquiv.symm.toEquiv.nontrivial
  have hroot : scalar ^ orderOf element = 1 := by
    apply smul_left_injective ℂ (show (1 : Module.End ℂ data.vector) ≠ 0 from one_ne_zero)
    calc
      scalar ^ orderOf element • (1 : Module.End ℂ data.vector) =
          (scalar • (1 : Module.End ℂ data.vector)) ^ orderOf element := by rw [smul_pow, one_pow]
      _ = data.representation element ^ orderOf element := by rw [hscalar]
      _ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      _ = (1 : ℂ) • (1 : Module.End ℂ data.vector) := (one_smul _ _).symm
  refine ⟨scalar, hroot, ?_⟩
  change LinearMap.trace ℂ data.vector (data.representation element) =
    scalar * LinearMap.trace ℂ data.vector (data.representation 1)
  rw [hscalar, map_smul, data.representation.map_one, smul_eq_mul]

theorem finite_character_value_isIntegral {G : Type*} [Group G] [Finite G]
    (data : FiniteComplexRepresentation G) (element : G) : IsIntegral ℤ (data.character element) := by
  let cyclic := Subgroup.zpowers element
  let : CommGroup cyclic := IsCyclic.commGroup
  let generator : cyclic := ⟨element, Subgroup.mem_zpowers element⟩
  let restricted := inflatedFiniteComplexRepresentation cyclic.subtype data
  obtain ⟨size, summand, hirreducible, hexpansion⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum restricted
  have hvalue : data.character element = ∑ label : Fin size, (summand label).character generator :=
    hexpansion generator
  rw [hvalue]
  apply IsIntegral.sum
  intro label _
  obtain ⟨scalar, hroot, hscalar⟩ := irreducible_central_character_root_value (summand label)
    (hirreducible label) generator (by
      rw [Subgroup.mem_center_iff]
      intro member
      exact mul_comm member generator)
  rw [hscalar]
  apply IsIntegral.mul
  · exact (mem_integralClosure_iff ℤ ℂ).mp
      (rootOfUnity_mem_complexAlgebraicIntegers scalar (orderOf generator) (orderOf_pos generator) hroot)
  · change IsIntegral ℤ ((summand label).representation.character 1)
    rw [Representation.char_one]
    exact isIntegral_algebraMap

theorem virtual_character_value_isIntegral {G : Type*} [Group G] [Finite G]
    (function : G → ℂ) (hvirtual : function ∈ virtualCharacters G) (element : G) :
    IsIntegral ℤ (function element) := by
  induction hvirtual using Submodule.span_induction with
  | mem character hmember =>
    obtain ⟨data, rfl⟩ := hmember
    exact finite_character_value_isIntegral data element
  | zero => exact isIntegral_zero
  | add left right _ _ hleft hright => exact hleft.add hright
  | smul scalar function _ hintegral =>
    change IsIntegral ℤ (scalar • function element)
    rw [zsmul_eq_mul]
    exact isIntegral_algebraMap.mul hintegral

end CFSG.TwoRankLowerBound.Helpers
