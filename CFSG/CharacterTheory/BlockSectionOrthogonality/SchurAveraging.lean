module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.PrimaryParts
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

theorem irreducible_character_one_ne_zero {G : Type*} [Group G]
    {space : Type*} [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
    (representation : Representation ℂ G space) [representation.IsIrreducible] :
    representation.character 1 ≠ 0 := by
  let := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) representation.asModule
  let : Nontrivial space := representation.asModuleEquiv.symm.nontrivial
  rw [Representation.char_one]
  exact_mod_cast Module.finrank_pos.ne'

theorem commuting_operator_eq_scalar {G : Type*} [Group G]
    {space : Type*} [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
    (representation : Representation ℂ G space) [representation.IsIrreducible]
    (operator : Module.End ℂ space)
    (hcommute : ∀ element, operator * representation element = representation element * operator) :
    ∃ scalar : ℂ, operator = scalar • LinearMap.id := by
  let intertwiner : representation.IntertwiningMap representation :=
    ⟨operator, hcommute⟩
  obtain ⟨scalar, hScalar⟩ :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2
      intertwiner
  refine ⟨scalar, ?_⟩
  have hLinear := congrArg Representation.IntertwiningMap.toLinearMap hScalar
  have hOne : (1 : representation.IntertwiningMap representation).toLinearMap =
      LinearMap.id := by
    ext vector
    rfl
  simpa [Representation.IntertwiningMap.algebraMap_apply, intertwiner, hOne] using hLinear.symm

@[expose] noncomputable def weightedCharacterOperator {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space]
    (representation : Representation ℂ G space) (weight : G → ℂ) : Module.End ℂ space :=
  ∑ element, weight element⁻¹ • representation element

theorem weightedCharacterOperator_commutes {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space]
    (representation : Representation ℂ G space) (weight : G → ℂ)
    (hweight : BlocksIsClassFunction weight) (element : G) :
    weightedCharacterOperator representation weight * representation element =
      representation element * weightedCharacterOperator representation weight := by
  classical
  have hReindex := Equiv.sum_comp (twoSidedPermutation element element)
    (fun index => weight index⁻¹ • representation (index * element))
  change (∑ index, weight index⁻¹ • representation index) * representation element =
    representation element * (∑ index, weight index⁻¹ • representation index)
  rw [Finset.sum_mul, Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, ← map_mul]
  rw [← hReindex]
  apply Finset.sum_congr rfl
  intro index hindex
  have hWeight : weight (twoSidedPermutation element element index)⁻¹ =
      weight index⁻¹ := by
    simpa only [twoSidedPermutation_apply, mul_inv_rev, inv_inv, mul_assoc] using
      hweight index⁻¹ element
  rw [hWeight]
  simp [mul_assoc]

theorem weightedCharacterOperator_trace {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space]
    (representation : Representation ℂ G space) (weight : G → ℂ) :
    LinearMap.trace ℂ space (weightedCharacterOperator representation weight) =
      ∑ element, weight element⁻¹ * representation.character element := by
  simp [weightedCharacterOperator, Representation.character]

theorem weightedCharacterOperator_eq_scalar {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
    (representation : Representation ℂ G space) [representation.IsIrreducible]
    (weight : G → ℂ) (hweight : BlocksIsClassFunction weight) :
    weightedCharacterOperator representation weight =
      ((∑ element, weight element⁻¹ * representation.character element) /
        representation.character 1) • LinearMap.id := by
  obtain ⟨scalar, hScalar⟩ := commuting_operator_eq_scalar representation
    (weightedCharacterOperator representation weight)
    (weightedCharacterOperator_commutes representation weight hweight)
  have hTrace := congrArg (LinearMap.trace ℂ space) hScalar
  rw [weightedCharacterOperator_trace, map_smul, LinearMap.trace_id,
    smul_eq_mul, ← Representation.char_one representation] at hTrace
  rw [hScalar, hTrace]
  rw [mul_div_cancel_right₀ _ (irreducible_character_one_ne_zero representation)]

theorem sum_character_conjugates {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
    (representation : Representation ℂ G space) [representation.IsIrreducible]
    (left right : G) :
    ∑ element, representation.character (left * element * right * element⁻¹) =
      (Nat.card G : ℂ) / representation.character 1 *
        representation.character left * representation.character right := by
  classical
  let operator : Module.End ℂ space :=
    ∑ element, representation (element * right * element⁻¹)
  have hCommute : ∀ conjugator, operator * representation conjugator =
      representation conjugator * operator := by
    intro conjugator
    have hReindex := Equiv.sum_comp (Equiv.mulLeft conjugator)
      (fun element => representation ((element * right * element⁻¹) * conjugator))
    dsimp [operator]
    rw [Finset.sum_mul, Finset.mul_sum]
    simp only [← map_mul]
    rw [← hReindex]
    apply Finset.sum_congr rfl
    intro element helement
    congr 1
    change (conjugator * element * right * (conjugator * element)⁻¹) * conjugator = _
    group
  obtain ⟨scalar, hScalar⟩ := commuting_operator_eq_scalar representation operator hCommute
  have hTrace := congrArg (LinearMap.trace ℂ space) hScalar
  have hTraceOperator : LinearMap.trace ℂ space operator =
      (Nat.card G : ℂ) * representation.character right := by
    change LinearMap.trace ℂ space (∑ element,
      representation (element * right * element⁻¹)) = _
    rw [map_sum]
    change (∑ element, representation.character (element * right * element⁻¹)) = _
    simp [Representation.char_conj, Nat.card_eq_fintype_card]
  rw [hTraceOperator, map_smul, LinearMap.trace_id, smul_eq_mul,
    ← Representation.char_one representation] at hTrace
  have hScalarValue : scalar =
      (Nat.card G : ℂ) * representation.character right / representation.character 1 := by
    apply (eq_div_iff (irreducible_character_one_ne_zero representation)).mpr
    exact hTrace.symm
  have hProductTrace : LinearMap.trace ℂ space (representation left * operator) =
      ∑ element, representation.character (left * element * right * element⁻¹) := by
    simp [operator, Finset.mul_sum, ← map_mul, mul_assoc, Representation.character]
  rw [← hProductTrace, hScalar, mul_smul_comm,
    show representation left * LinearMap.id = representation left from mul_one _,
    map_smul, smul_eq_mul]
  change scalar * representation.character left = _
  rw [hScalarValue]
  ring

end CFSG.BlockSectionOrthogonality.Helpers
