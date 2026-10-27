module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterSubsetProjection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem complex_root_conjugate_inverse {root : ℂ} {period : ℕ}
    (hroot : root ^ period = 1) (hperiod : period ≠ 0) :
    starRingEnd ℂ root = root⁻¹ := by
  have hnorm : Complex.normSq root = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_eq_one_of_pow_eq_one hroot hperiod, one_pow]
  symm
  apply inv_eq_of_mul_eq_one_left
  rw [mul_comm, Complex.mul_conj, hnorm, Complex.ofReal_one]

theorem finite_character_conjugate_inverse {group : Type*} [Group group] [Finite group]
    (data : FiniteComplexRepresentation group) (element : group) :
    starRingEnd ℂ (data.character element) = data.character element⁻¹ := by
  let cyclic := Subgroup.zpowers element
  let : CommGroup cyclic := IsCyclic.commGroup
  let generator : cyclic := ⟨element, Subgroup.mem_zpowers element⟩
  let restricted := inflatedFiniteComplexRepresentation cyclic.subtype data
  obtain ⟨size, summand, hirreducible, hexpansion⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum restricted
  have hleft : data.character element = ∑ label : Fin size, (summand label).character generator :=
    hexpansion generator
  have hright : data.character element⁻¹ = ∑ label : Fin size, (summand label).character generator⁻¹ :=
    hexpansion generator⁻¹
  rw [hleft, hright, map_sum]
  apply Finset.sum_congr rfl
  intro label _
  obtain ⟨scalar, hroot, hscalar⟩ := irreducible_central_character_root_value (summand label)
    (hirreducible label) generator (by rw [Subgroup.mem_center_iff]; exact fun member => mul_comm member generator)
  let : (summand label).representation.IsIrreducible := hirreducible label
  obtain ⟨operatorScalar, hoperator⟩ := irreducible_central_element_is_scalar (summand label).representation
    generator (by rw [Subgroup.mem_center_iff]; exact fun member => mul_comm member generator)
  have htrace : (summand label).character generator = operatorScalar * (summand label).character 1 := by
    change LinearMap.trace ℂ (summand label).vector ((summand label).representation generator) = _
    rw [hoperator, map_smul, LinearMap.trace_one, smul_eq_mul,
      FiniteComplexRepresentation.character, Representation.char_one]
  have hequal : operatorScalar = scalar := by
    exact mul_right_cancel₀ (irreducible_character_degree_ne_zero _ (hirreducible label)) (htrace.symm.trans hscalar)
  rw [hequal] at hoperator
  have hinverseOperator : (summand label).representation generator⁻¹ =
      scalar⁻¹ • (1 : Module.End ℂ (summand label).vector) := by
    have hnonzero : scalar ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow (orderOf_pos generator).ne'] at hroot
      exact zero_ne_one hroot
    have hproduct := (summand label).representation.map_mul generator generator⁻¹
    rw [mul_inv_cancel, map_one, hoperator, smul_mul_assoc, one_mul] at hproduct
    have hscaled := congrArg (fun operator => scalar⁻¹ • operator) hproduct
    rw [smul_smul, inv_mul_cancel₀ hnonzero, one_smul] at hscaled
    exact hscaled.symm
  rw [hscalar, map_mul, complex_root_conjugate_inverse hroot (orderOf_pos generator).ne']
  rw [FiniteComplexRepresentation.character, Representation.char_one, map_natCast]
  change _ = LinearMap.trace ℂ (summand label).vector ((summand label).representation generator⁻¹)
  rw [hinverseOperator, map_smul, LinearMap.trace_one, smul_eq_mul]

theorem virtual_character_conjugate_inverse {group : Type*} [Group group] [Finite group]
    (function : group → ℂ) (hfunction : function ∈ virtualCharacters group) (element : group) :
    starRingEnd ℂ (function element) = function element⁻¹ := by
  induction hfunction using Submodule.span_induction with
  | mem character hmember =>
    obtain ⟨data, rfl⟩ := hmember
    exact finite_character_conjugate_inverse data element
  | zero => exact map_zero _
  | add left right _ _ hleft hright =>
    simp only [Pi.add_apply, map_add, hleft, hright]
  | smul scalar function _ hequal =>
    simp only [Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast, hequal]

theorem characterPairing_mask_character_pos {group : Type*} [Group group] [Fintype group]
    (domain : Set group) (data : FiniteComplexRepresentation group)
    (hactive : ∃ element ∈ domain, data.character element ≠ 0) :
    0 < (characterPairing (characterFunctionMask domain data.character) data.character).re := by
  have hterm : ∀ element : group,
      characterFunctionMask domain data.character element * data.character element⁻¹ =
        if element ∈ domain then (Complex.normSq (data.character element) : ℂ) else 0 := by
    intro element
    rw [← finite_character_conjugate_inverse data element]
    by_cases hmember : element ∈ domain
    · rw [characterFunctionMask, ite_eq_left hmember, ite_eq_left hmember, Complex.mul_conj]
    · rw [characterFunctionMask, ite_eq_right hmember, ite_eq_right hmember, zero_mul]
  have hsum : 0 < ∑ element : group, if element ∈ domain then Complex.normSq (data.character element) else 0 := by
    apply Finset.sum_pos'
    · intro element _
      split_ifs
      · exact Complex.normSq_nonneg _
      · exact le_rfl
    · obtain ⟨element, hmember, hnonzero⟩ := hactive
      exact ⟨element, Finset.mem_univ _, by rw [ite_eq_left hmember]; exact Complex.normSq_pos.mpr hnonzero⟩
  unfold characterPairing
  simp_rw [hterm]
  have hequal : (∑ element : group,
      if element ∈ domain then (Complex.normSq (data.character element) : ℂ) else 0) =
      ((∑ element : group, if element ∈ domain then Complex.normSq (data.character element) else 0 : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro element _
    split_ifs <;> simp
  rw [hequal]
  have hcard : (Nat.card group : ℂ)⁻¹ = (((Nat.card group : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [hcard, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_pos (inv_pos.mpr (by exact_mod_cast Nat.card_pos (α := group))) hsum

end CFSG.TwoRankLowerBound.Helpers
