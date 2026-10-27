module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterSubsetProjection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem characterSubsetProjection_pairing_left {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (left right : group → ℂ) :
    characterPairing (characterSubsetProjection basis support left) right =
      ∑ label ∈ support, characterPairing left (basis.representation label).character *
        characterPairing (basis.representation label).character right := by
  let coefficient := fun label => characterPairing left (basis.representation label).character
  have hfunction : characterSubsetProjection basis support left =
      fun element => ∑ label ∈ support,
        coefficient label * (basis.representation label).character element := by
    funext element
    simp only [characterSubsetProjection, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coefficient]
  rw [hfunction]
  change (Nat.card group : ℂ)⁻¹ *
      ∑ element, (∑ label ∈ support,
        coefficient label * (basis.representation label).character element) * right element⁻¹ =
    ∑ label ∈ support, coefficient label *
      ((Nat.card group : ℂ)⁻¹ * ∑ element,
        (basis.representation label).character element * right element⁻¹)
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label _
  rw [← Finset.mul_sum]
  ring

theorem characterSubsetProjection_pairing_self_adjoint {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (support : Finset basis.index) (left right : group → ℂ) :
    characterPairing (characterSubsetProjection basis support left) right =
      characterPairing left (characterSubsetProjection basis support right) := by
  rw [characterSubsetProjection_pairing_left, characterPairing_comm left,
    characterSubsetProjection_pairing_left]
  apply Finset.sum_congr rfl
  intro label _
  rw [characterPairing_comm (basis.representation label).character right,
    characterPairing_comm (basis.representation label).character left, mul_comm]

theorem coefficientCharacterSpace_pairing_projection_right {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (support : Finset basis.index) (left right : group → ℂ)
    (hleft : left ∈ coefficientCharacterSpace basis support) :
    characterPairing left right =
      characterPairing left (characterSubsetProjection basis support right) := by
  rw [← characterSubsetProjection_pairing_self_adjoint,
    characterSubsetProjection_identity basis support left hleft]

theorem characterPairing_zero_of_inverse_support {group : Type*} [Group group] [Fintype group]
    (domain : Set group) (left right : group → ℂ)
    (hsupport : ∀ element, element ∉ domain → left element = 0)
    (hzero : ∀ element, element ∈ domain → right element⁻¹ = 0) :
    characterPairing left right = 0 := by
  unfold characterPairing
  have hsum : ∑ element : group, left element * right element⁻¹ = 0 := by
    apply Finset.sum_eq_zero
    intro element _
    by_cases hmember : element ∈ domain
    · rw [hzero element hmember, mul_zero]
    · rw [hsupport element hmember, zero_mul]
  rw [hsum, mul_zero]

theorem coefficientCharacterSpace_pairing_zero_of_projected_inverse_support {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (support : Finset basis.index) (domain : Set group) (left right : group → ℂ)
    (hleft : left ∈ coefficientCharacterSpace basis support)
    (hsupport : ∀ element, element ∉ domain → left element = 0)
    (hzero : ∀ element, element ∈ domain →
      characterSubsetProjection basis support right element⁻¹ = 0) :
    characterPairing left right = 0 := by
  rw [coefficientCharacterSpace_pairing_projection_right basis support left right hleft]
  exact characterPairing_zero_of_inverse_support domain left _ hsupport hzero

end CFSG.TwoRankLowerBound.Helpers
