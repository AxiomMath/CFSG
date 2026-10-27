module

public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteCharacters

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

universe groupUniverse vectorUniverse

@[expose] noncomputable def weightedCharacterOperator {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ G vector)
    (function : G → ℂ) : Module.End ℂ vector :=
  ∑ element : G, function element⁻¹ • representation element

theorem weightedCharacterOperator_commutes {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ G vector)
    (function : G → ℂ)
    (hclass : ∀ element conjugator : G, function (conjugator * element * conjugator⁻¹) = function element)
    (conjugator : G) : Commute (weightedCharacterOperator representation function)
      (representation conjugator) := by
  have hsum : (∑ element : G, function (conjugator * element * conjugator⁻¹)⁻¹ •
      representation (conjugator * element * conjugator⁻¹)) =
      weightedCharacterOperator representation function := by
    apply Fintype.sum_equiv (MulAut.conj conjugator).toEquiv
    intro element
    rfl
  unfold weightedCharacterOperator at hsum ⊢
  change (∑ element : G, function element⁻¹ • representation element) * representation conjugator =
    representation conjugator * ∑ element : G, function element⁻¹ • representation element
  conv_lhs => rw [← hsum]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro element _
  have hinverse : (conjugator * element * conjugator⁻¹)⁻¹ =
      conjugator * element⁻¹ * conjugator⁻¹ := by group
  rw [hinverse, hclass, smul_mul_assoc, mul_smul_comm, ← map_mul, ← map_mul]
  congr 2
  group

theorem irreducible_weightedCharacterOperator_scalar {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) [representation.IsIrreducible]
    (function : G → ℂ)
    (hclass : ∀ element conjugator : G, function (conjugator * element * conjugator⁻¹) = function element) :
    ∃ scalar : ℂ, weightedCharacterOperator representation function =
      scalar • (1 : Module.End ℂ vector) := by
  let intertwiner : representation.IntertwiningMap representation :=
    { toLinearMap := weightedCharacterOperator representation function
      isIntertwining' := weightedCharacterOperator_commutes representation function hclass }
  obtain ⟨scalar, hscalar⟩ :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 intertwiner
  refine ⟨scalar, ?_⟩
  have hequal := congrArg Representation.IntertwiningMap.toLinearMap hscalar
  rw [Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul] at hequal
  have hone : (1 : representation.IntertwiningMap representation).toLinearMap =
      (1 : Module.End ℂ vector) := by
    ext element
    exact congrFun (Representation.IntertwiningMap.coe_one representation) element
  rw [hone] at hequal
  exact hequal.symm

theorem weightedCharacterOperator_trace {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) (function : G → ℂ) :
    LinearMap.trace ℂ vector (weightedCharacterOperator representation function) =
      (Nat.card G : ℂ) * characterPairing function representation.character := by
  rw [weightedCharacterOperator, map_sum]
  simp only [map_smul]
  change (∑ element : G, function element⁻¹ * representation.character element) = _
  rw [characterPairing, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]
  apply Fintype.sum_equiv (Equiv.inv G)
  intro element
  simp

theorem irreducible_weightedCharacterOperator_zero {G : Type groupUniverse} [Group G] [Fintype G]
    (data : FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G) (hirreducible : data.IsIrreducible)
    (function : G → ℂ)
    (hclass : ∀ element conjugator : G, function (conjugator * element * conjugator⁻¹) = function element)
    (hpair : characterPairing function data.character = 0) :
    weightedCharacterOperator data.representation function = 0 := by
  let : data.representation.IsIrreducible := hirreducible
  obtain ⟨scalar, hscalar⟩ := irreducible_weightedCharacterOperator_scalar data.representation function hclass
  have htrace := weightedCharacterOperator_trace data.representation function
  rw [hscalar, map_smul, LinearMap.trace_one, ← Representation.char_one data.representation] at htrace
  change scalar * data.character 1 = (Nat.card G : ℂ) * characterPairing function data.character at htrace
  rw [hpair, mul_zero] at htrace
  have hzero := (mul_eq_zero.mp htrace).resolve_right
    (irreducible_character_degree_ne_zero data hirreducible)
  rw [hscalar, hzero, zero_smul]

end CFSG.TwoRankLowerBound.Helpers
