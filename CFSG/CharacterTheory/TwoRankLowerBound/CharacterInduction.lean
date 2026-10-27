module

public import CFSG.CharacterTheory.TwoRankLowerBound.RootInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.PiTrace

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

noncomputable def coinductionAverage {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] (subgroup : Subgroup G)
    (representation : Representation ℂ subgroup vector) : Module.End ℂ (G → vector) := by
  classical
  exact (Nat.card subgroup : ℂ)⁻¹ • ∑ member : subgroup,
    (representation member).compLeft G ∘ₗ
      LinearMap.funLeft ℂ vector (fun element : G => (member : G)⁻¹ * element)

theorem coinductionAverage_apply {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] (subgroup : Subgroup G)
    (representation : Representation ℂ subgroup vector) (function : G → vector)
    (element : G) :
    coinductionAverage subgroup representation function element =
      (Nat.card subgroup : ℂ)⁻¹ • ∑ member : subgroup,
        representation member (function ((member : G)⁻¹ * element)) := by
  classical
  simp [coinductionAverage, LinearMap.sum_apply, Finset.sum_apply]

theorem coinductionAverage_mem {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] (subgroup : Subgroup G)
    (representation : Representation ℂ subgroup vector) (function : G → vector) :
    coinductionAverage subgroup representation function ∈
      Representation.coindV subgroup.subtype representation := by
  classical
  intro member element
  simp only [coinductionAverage_apply, map_smul, map_sum]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft member⁻¹)
  intro other
  change representation other (function ((other : G)⁻¹ * ((member : G) * element))) =
    representation member
      (representation (member⁻¹ * other)
        (function (((member⁻¹ * other : subgroup) : G)⁻¹ * element)))
  simp [mul_assoc, ← Module.End.mul_apply, ← map_mul]

theorem coinductionAverage_eq_self {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] (subgroup : Subgroup G)
    (representation : Representation ℂ subgroup vector)
    (function : Representation.coindV subgroup.subtype representation) :
    coinductionAverage subgroup representation function = function := by
  classical
  ext element
  rw [coinductionAverage_apply]
  have hterm : ∀ member : subgroup,
      representation member ((function : G → vector) ((member : G)⁻¹ * element)) =
        (function : G → vector) element := by
    intro member
    have hequiv := function.property member ((member : G)⁻¹ * element)
    simpa [mul_assoc] using hequiv.symm
  simp only [hterm, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.card_pos.ne')), one_smul]

noncomputable def coinductionAverageTo {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] (subgroup : Subgroup G)
    (representation : Representation ℂ subgroup vector) :
    (G → vector) →ₗ[ℂ] Representation.coindV subgroup.subtype representation :=
  (coinductionAverage subgroup representation).codRestrict
    (Representation.coindV subgroup.subtype representation)
    (coinductionAverage_mem subgroup representation)

theorem coinduction_character_eq_average_trace {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (subgroup : Subgroup G) (representation : Representation ℂ subgroup vector)
    (element : G) :
    (Representation.coind subgroup.subtype representation).character element =
      LinearMap.trace ℂ (G → vector)
        (coinductionAverage subgroup representation ∘ₗ
          LinearMap.funLeft ℂ vector (fun argument : G => argument * element)) := by
  let inclusion := (Representation.coindV subgroup.subtype representation).subtype
  let projection := coinductionAverageTo subgroup representation
  have hcoind : (projection ∘ₗ
      LinearMap.funLeft ℂ vector (fun argument : G => argument * element)) ∘ₗ inclusion =
      Representation.coind subgroup.subtype representation element := by
    ext function argument
    change coinductionAverage subgroup representation
      ((Representation.coind subgroup.subtype representation element function :
        Representation.coindV subgroup.subtype representation) : G → vector) argument = _
    rw [coinductionAverage_eq_self]
  have htrace := LinearMap.trace_comp_comm'
    (projection ∘ₗ LinearMap.funLeft ℂ vector (fun argument : G => argument * element)) inclusion
  rw [hcoind] at htrace
  exact htrace.symm

theorem coinduction_summand_trace {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (subgroup : Subgroup G) (representation : Representation ℂ subgroup vector)
    (member : subgroup) (element : G) :
    LinearMap.trace ℂ (G → vector)
      ((representation member).compLeft G ∘ₗ
        LinearMap.funLeft ℂ vector (fun argument : G => (member : G)⁻¹ * argument) ∘ₗ
          LinearMap.funLeft ℂ vector (fun argument : G => argument * element)) =
      ∑ argument : G, if (member : G) = argument * element * argument⁻¹
        then representation.character member else 0 := by
  classical
  rw [trace_pi_coordinate_operator _
    (fun argument : G => (member : G)⁻¹ * argument * element)
    (fun _argument => representation member) (by intros; rfl)]
  apply Finset.sum_congr rfl
  intro argument _
  have hfixed : (member : G)⁻¹ * argument * element = argument ↔
      (member : G) = argument * element * argument⁻¹ := by
    constructor
    · intro hequal
      have hequal' := congrArg (fun value : G => (member : G) * value * argument⁻¹) hequal
      simpa [mul_assoc] using hequal'.symm
    · intro hequal
      rw [hequal]
      group
  simp only [hfixed, Representation.character]

theorem subgroup_sum_value_delta {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (function : subgroup → ℂ) (element : G) :
    (∑ member : subgroup, if (member : G) = element then function member else 0) =
      if hmember : element ∈ subgroup then function ⟨element, hmember⟩ else 0 := by
  classical
  split_ifs with hmember
  · rw [Fintype.sum_eq_single (⟨element, hmember⟩ : subgroup)]
    · simp
    · intro member hne
      have hvalue : (member : G) ≠ element := fun hequal => hne (Subtype.ext hequal)
      simp [hvalue]
  · apply Finset.sum_eq_zero
    intro member _
    have hvalue : (member : G) ≠ element := fun hequal =>
      hmember (hequal ▸ member.property)
    simp [hvalue]

theorem coinduction_character_eq_inducedFunction {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (subgroup : Subgroup G) (representation : Representation ℂ subgroup vector)
    (element : G) :
    (Representation.coind subgroup.subtype representation).character element =
      inducedFunction subgroup representation.character element := by
  classical
  rw [coinduction_character_eq_average_trace]
  unfold coinductionAverage
  change LinearMap.trace ℂ (G → vector)
    (((Nat.card subgroup : ℂ)⁻¹ • ∑ member : subgroup,
      (representation member).compLeft G ∘ₗ
        LinearMap.funLeft ℂ vector (fun argument : G => (member : G)⁻¹ * argument)) *
      LinearMap.funLeft ℂ vector (fun argument : G => argument * element)) = _
  rw [smul_mul_assoc, Finset.sum_mul, map_smul, map_sum]
  simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc,
    coinduction_summand_trace, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [subgroup_sum_value_delta]
  unfold inducedFunction
  congr 1
  apply Fintype.sum_equiv (Equiv.inv G)
  intro argument
  simp only [Equiv.inv_apply, inv_inv]

end CFSG.TwoRankLowerBound.Helpers
