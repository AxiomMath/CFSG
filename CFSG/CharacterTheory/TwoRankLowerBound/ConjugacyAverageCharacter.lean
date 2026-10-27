module

public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteCharacters

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

noncomputable def conjugacyAverageOperator {group vector : Type*} [Group group] [Fintype group]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ group vector)
    (element : group) : Module.End ℂ vector :=
  ∑ conjugator : group, representation (conjugator * element * conjugator⁻¹)

theorem conjugacyAverageOperator_commute {group vector : Type*} [Group group] [Fintype group]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ group vector)
    (element member : group) : Commute (conjugacyAverageOperator representation element) (representation member) := by
  have hsum : (∑ conjugator : group, representation
      (member * (conjugator * element * conjugator⁻¹) * member⁻¹)) =
      conjugacyAverageOperator representation element := by
    unfold conjugacyAverageOperator
    apply Fintype.sum_equiv (Equiv.mulLeft member)
    intro conjugator
    congr 1
    change member * (conjugator * element * conjugator⁻¹) * member⁻¹ =
      (member * conjugator) * element * (member * conjugator)⁻¹
    group
  change conjugacyAverageOperator representation element * representation member =
    representation member * conjugacyAverageOperator representation element
  calc
    _ = (∑ conjugator : group, representation
        (member * (conjugator * element * conjugator⁻¹) * member⁻¹)) * representation member := by rw [hsum]
    _ = ∑ conjugator : group, representation member *
        representation (conjugator * element * conjugator⁻¹) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro conjugator _
      rw [← map_mul]
      have hequal : member * (conjugator * element * conjugator⁻¹) * member⁻¹ * member =
          member * (conjugator * element * conjugator⁻¹) := by group
      rw [hequal, map_mul]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem irreducible_conjugacyAverageOperator_scalar {group vector : Type*}
    [Group group] [Fintype group] [AddCommGroup vector] [Module ℂ vector]
    [FiniteDimensional ℂ vector] (representation : Representation ℂ group vector)
    [representation.IsIrreducible] (element : group) :
    ∃ scalar : ℂ, conjugacyAverageOperator representation element =
      scalar • (1 : Module.End ℂ vector) := by
  let intertwiner : representation.IntertwiningMap representation :=
    { toLinearMap := conjugacyAverageOperator representation element
      isIntertwining' := fun member => conjugacyAverageOperator_commute representation element member }
  obtain ⟨scalar, hscalar⟩ :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 intertwiner
  have hequal := congrArg Representation.IntertwiningMap.toLinearMap hscalar
  rw [Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul] at hequal
  have hone : (1 : representation.IntertwiningMap representation).toLinearMap =
      (1 : Module.End ℂ vector) := by
    apply LinearMap.ext
    intro value
    exact congrFun (Representation.IntertwiningMap.coe_one representation) value
  rw [hone] at hequal
  exact ⟨scalar, hequal.symm⟩

theorem irreducible_conjugacyAverageOperator_formula {group : Type*} [Group group] [Fintype group]
    (data : FiniteComplexRepresentation group) (hirreducible : data.IsIrreducible) (element : group) :
    conjugacyAverageOperator data.representation element =
      ((Nat.card group : ℂ) * data.character element / data.character 1) •
        (1 : Module.End ℂ data.vector) := by
  let : data.representation.IsIrreducible := hirreducible
  obtain ⟨scalar, hscalar⟩ := irreducible_conjugacyAverageOperator_scalar data.representation element
  have htrace := congrArg (LinearMap.trace ℂ data.vector) hscalar
  simp only [conjugacyAverageOperator, map_sum, map_smul, LinearMap.trace_one,
    ← Representation.char_one data.representation, smul_eq_mul] at htrace
  change (∑ conjugator : group, data.character (conjugator * element * conjugator⁻¹)) =
    scalar * data.character 1 at htrace
  simp only [Representation.char_conj] at htrace
  have hconstant : (∑ _ : group, data.character element) = (Nat.card group : ℂ) * data.character element := by
    simp [Nat.card_eq_fintype_card]
  rw [hconstant] at htrace
  have hformula : scalar = (Nat.card group : ℂ) * data.character element / data.character 1 :=
    (eq_div_iff (irreducible_character_degree_ne_zero data hirreducible)).mpr htrace.symm
  rw [hscalar, hformula]

theorem irreducible_conjugacyAverage_character {group : Type*} [Group group] [Fintype group]
    (data : FiniteComplexRepresentation group) (hirreducible : data.IsIrreducible) (left right : group) :
    (∑ conjugator : group, data.character (left * (conjugator * right * conjugator⁻¹))) =
      (Nat.card group : ℂ) * data.character left * data.character right / data.character 1 := by
  have htrace := congrArg
    (fun operator : Module.End ℂ data.vector => LinearMap.trace ℂ data.vector (data.representation left * operator))
    (irreducible_conjugacyAverageOperator_formula data hirreducible right)
  simp only [conjugacyAverageOperator, Finset.mul_sum, map_sum, ← map_mul,
    mul_smul_comm, map_smul, mul_one, smul_eq_mul] at htrace
  change (∑ conjugator : group, data.character (left * (conjugator * right * conjugator⁻¹))) =
    ((Nat.card group : ℂ) * data.character right / data.character 1) * data.character left at htrace
  rw [htrace]
  ring

end CFSG.TwoRankLowerBound.Helpers
