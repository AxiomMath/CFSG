module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasis

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def groupAlgebraClassElement {G : Type*} [Group G] [Fintype G]
    (function : G → ℂ) : MonoidAlgebra ℂ G :=
  ∑ element : G, MonoidAlgebra.single element (function element⁻¹)

theorem groupAlgebraClassElement_coeff {G : Type*} [Group G] [Fintype G]
    (function : G → ℂ) (element : G) :
    (groupAlgebraClassElement function).coeff element = function element⁻¹ := by
  simp only [groupAlgebraClassElement, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem groupAlgebraClassElement_action {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] (representation : Representation ℂ G vector)
    (function : G → ℂ) :
    representation.asAlgebraHom (groupAlgebraClassElement function) =
      weightedCharacterOperator representation function := by
  simp only [groupAlgebraClassElement, map_sum, Representation.asAlgebraHom_single,
    weightedCharacterOperator]

theorem leftRegular_algebra_action_injective {G : Type*} [Group G] :
    Function.Injective (Representation.leftRegular ℂ G).asAlgebraHom := by
  intro left right hequal
  have heval := congrArg (fun operator : Module.End ℂ (MonoidAlgebra ℂ G) => operator 1) hequal
  simpa only [Representation.asAlgebraHom_ofMulAction_smul_eq_mul, mul_one] using heval

theorem groupAlgebraClassElement_central {G : Type*} [Group G] [Fintype G]
    (function : G → ℂ)
    (hclass : ∀ element conjugator : G,
      function (conjugator * element * conjugator⁻¹) = function element) :
    ∀ other : MonoidAlgebra ℂ G, Commute (groupAlgebraClassElement function) other := by
  intro other
  induction other using MonoidAlgebra.induction_on with
  | of element =>
    apply leftRegular_algebra_action_injective
    simp only [map_mul, groupAlgebraClassElement_action, Representation.asAlgebraHom_of]
    exact weightedCharacterOperator_commutes (Representation.leftRegular ℂ G) function hclass element
  | add left right hleft hright => exact hleft.add_right hright
  | smul scalar element helement => exact helement.smul_right scalar

theorem central_groupAlgebra_coeff_conjugation {G : Type*} [Group G]
    (algebraElement : MonoidAlgebra ℂ G)
    (hcentral : ∀ other : MonoidAlgebra ℂ G, Commute algebraElement other)
    (element conjugator : G) :
    algebraElement.coeff (conjugator * element * conjugator⁻¹) = algebraElement.coeff element := by
  have hequal := congrArg (fun value : MonoidAlgebra ℂ G => value.coeff (conjugator * element))
    (hcentral (MonoidAlgebra.single conjugator 1)).eq
  simpa only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply,
    mul_one, one_mul, inv_mul_cancel_left] using hequal

theorem groupAlgebraClassElement_of_coeff {G : Type*} [Group G] [Fintype G]
    (algebraElement : MonoidAlgebra ℂ G) :
    groupAlgebraClassElement (fun element => algebraElement.coeff element⁻¹) = algebraElement := by
  ext element
  simp only [groupAlgebraClassElement_coeff, inv_inv]

theorem central_groupAlgebra_eq_zero_of_basis_actions {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (algebraElement : MonoidAlgebra ℂ G)
    (hcentral : ∀ other : MonoidAlgebra ℂ G, Commute algebraElement other)
    (hzero : ∀ label, (basis.representation label).representation.asAlgebraHom algebraElement = 0) :
    algebraElement = 0 := by
  let function : G → ℂ := fun element => algebraElement.coeff element⁻¹
  have hclass : ∀ element conjugator : G,
      function (conjugator * element * conjugator⁻¹) = function element := by
    intro element conjugator
    have hinverse : (conjugator * element * conjugator⁻¹)⁻¹ =
        conjugator * element⁻¹ * conjugator⁻¹ := by group
    change algebraElement.coeff (conjugator * element * conjugator⁻¹)⁻¹ =
      algebraElement.coeff element⁻¹
    rw [hinverse]
    exact central_groupAlgebra_coeff_conjugation algebraElement hcentral element⁻¹ conjugator
  have hfunction : function = 0 := by
    apply basis.separates function hclass
    intro label
    have haction : weightedCharacterOperator (basis.representation label).representation function = 0 := by
      rw [← groupAlgebraClassElement_action, groupAlgebraClassElement_of_coeff]
      exact hzero label
    have htrace := weightedCharacterOperator_trace (basis.representation label).representation function
    rw [haction, map_zero] at htrace
    exact (mul_eq_zero.mp htrace.symm).resolve_left (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  ext element
  have heval := congrFun hfunction element⁻¹
  simpa only [function, inv_inv, Pi.zero_apply, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using heval

theorem irreducible_weightedCharacterOperator_formula {G : Type*} [Group G] [Fintype G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (function : G → ℂ)
    (hclass : ∀ element conjugator : G,
      function (conjugator * element * conjugator⁻¹) = function element) :
    weightedCharacterOperator data.representation function =
      ((Nat.card G : ℂ) * characterPairing function data.character / data.character 1) •
        (1 : Module.End ℂ data.vector) := by
  let : data.representation.IsIrreducible := hirreducible
  obtain ⟨scalar, hscalar⟩ := irreducible_weightedCharacterOperator_scalar data.representation function hclass
  have htrace := weightedCharacterOperator_trace data.representation function
  rw [hscalar, map_smul, LinearMap.trace_one, ← Representation.char_one data.representation] at htrace
  change scalar * data.character 1 = _ at htrace
  have hequal : scalar = (Nat.card G : ℂ) * characterPairing function data.character / data.character 1 :=
    (eq_div_iff (irreducible_character_degree_ne_zero data hirreducible)).mpr htrace
  rw [hscalar, hequal]

@[expose] noncomputable def complexCharacterIdempotent {G : Type*} [Group G] [Fintype G]
    (character : G → ℂ) : MonoidAlgebra ℂ G :=
  (character 1 / (Nat.card G : ℂ)) • groupAlgebraClassElement character

theorem complexCharacterIdempotent_coeff {G : Type*} [Group G] [Fintype G]
    (character : G → ℂ) (element : G) :
    (complexCharacterIdempotent character).coeff element =
      character 1 / (Nat.card G : ℂ) * character element⁻¹ := by
  simp only [complexCharacterIdempotent, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    groupAlgebraClassElement_coeff, smul_eq_mul]

theorem complexCharacterIdempotent_central {G : Type*} [Group G] [Fintype G]
    (data : FiniteComplexRepresentation G) :
    ∀ other : MonoidAlgebra ℂ G, Commute (complexCharacterIdempotent data.character) other := by
  intro other
  apply (groupAlgebraClassElement_central data.character
    (Representation.char_conj data.representation) other).smul_left

theorem complexCharacterIdempotent_irreducible_action {G : Type*} [Group G] [Fintype G]
    (source target : FiniteComplexRepresentation G)
    (hsource : source.IsIrreducible) (htarget : target.IsIrreducible) :
    target.representation.asAlgebraHom (complexCharacterIdempotent source.character) =
      if source.character = target.character then 1 else 0 := by
  rw [complexCharacterIdempotent, map_smul, groupAlgebraClassElement_action,
    irreducible_weightedCharacterOperator_formula target htarget source.character
      (Representation.char_conj source.representation), smul_smul,
    characterPairing_irreducible source target hsource htarget]
  by_cases hequal : source.character = target.character
  · rw [ite_eq_left hequal, ite_eq_left hequal, hequal]
    have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hdegree := irreducible_character_degree_ne_zero target htarget
    have hscalar : target.character 1 / (Nat.card G : ℂ) *
        ((Nat.card G : ℂ) * 1 / target.character 1) = 1 := by field_simp
    rw [hscalar, one_smul]
  · rw [ite_eq_right hequal, ite_eq_right hequal]
    simp only [mul_zero, zero_div, zero_smul]

end CFSG.TwoRankLowerBound.Helpers
