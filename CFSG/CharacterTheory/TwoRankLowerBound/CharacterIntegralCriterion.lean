module

public import CFSG.CharacterTheory.TwoRankLowerBound.InductionPairing
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualPairingIntegral
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasis

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem virtualCharacter_iff_integer_basis_pairings {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (function : G → ℂ)
    (hclass : ∀ element conjugator : G, function (conjugator * element * conjugator⁻¹) = function element) :
    function ∈ virtualCharacters G ↔
      ∀ label, ∃ integer : ℤ, characterPairing function (basis.representation label).character = integer := by
  constructor
  · intro hvirtual label
    exact characterPairing_virtual_irreducible_integer function hvirtual (basis.representation label)
      (basis.irreducible label)
  · intro hpairings
    choose coefficient hcoefficient using hpairings
    have hexpansion : function = ∑ label, coefficient label • (basis.representation label).character := by
      funext element
      simp only [Finset.sum_apply, Pi.smul_apply]
      simpa only [zsmul_eq_mul, hcoefficient] using
        finiteIrreducibleCharacterBasis_reconstruction basis function hclass element
    rw [hexpansion]
    apply Submodule.sum_mem
    intro label _
    exact Submodule.smul_mem _ (coefficient label) (character_mem_virtualCharacters _)

theorem characterPairing_comm {G : Type*} [Group G] [Fintype G] (left right : G → ℂ) :
    characterPairing left right = characterPairing right left := by
  unfold characterPairing
  congr 1
  apply Fintype.sum_equiv (Equiv.inv G)
  intro element
  simp only [Equiv.inv_apply, inv_inv, mul_comm]

theorem characterPairing_inducedFunction_right {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (function : subgroup → ℂ) (classFunction : G → ℂ)
    (hclass : ∀ element conjugator : G,
      classFunction (conjugator * element * conjugator⁻¹) = classFunction element) :
    characterPairing classFunction (inducedFunction subgroup function) =
      characterPairing (fun element : subgroup => classFunction element) function := by
  rw [characterPairing_comm, characterPairing_inducedFunction_left subgroup function classFunction hclass,
    characterPairing_comm]

theorem inducedFunction_projection_formula {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (function : subgroup → ℂ) (classFunction : G → ℂ)
    (hclass : ∀ element conjugator : G,
      classFunction (conjugator * element * conjugator⁻¹) = classFunction element) :
    classFunction * inducedFunction subgroup function =
      inducedFunction subgroup (fun member => classFunction member * function member) := by
  funext element
  simp only [Pi.mul_apply, inducedFunction]
  rw [← mul_assoc, mul_comm (classFunction element), mul_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro conjugator _
  split_ifs with hmember
  · have hequal := hclass element conjugator⁻¹
    simp only [inv_inv] at hequal
    rw [hequal]
  · simp only [mul_zero]

end CFSG.TwoRankLowerBound.Helpers
