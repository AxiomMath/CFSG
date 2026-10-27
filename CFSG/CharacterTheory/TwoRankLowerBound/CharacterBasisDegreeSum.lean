module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionEightCharacters
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralIdempotentSpectral

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem finiteIrreducibleCharacterBasis_sum_degree_sq {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) :
    ∑ label, (basis.representation label).character 1 ^ 2 = (Nat.card G : ℂ) := by
  have hequal := congrArg (fun value : MonoidAlgebra ℂ G => value.coeff 1)
    (characterIdempotentExpansion_one basis)
  simp only [characterIdempotentExpansion, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, one_smul, complexCharacterIdempotent,
    groupAlgebraClassElement_coeff, inv_one, smul_eq_mul] at hequal
  have hone : (1 : MonoidAlgebra ℂ G).coeff 1 = 1 := by simp
  rw [hone] at hequal
  have hsum : ∑ label, (basis.representation label).character 1 / (Nat.card G : ℂ) *
      (basis.representation label).character 1 =
      (∑ label, (basis.representation label).character 1 ^ 2) / (Nat.card G : ℂ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro label _
    ring
  rw [hsum] at hequal
  exact (div_eq_one_iff_eq (Nat.cast_ne_zero.mpr Nat.card_pos.ne')).mp hequal

theorem finiteIrreducibleCharacterBasis_sum_finrank_sq {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) :
    ∑ label, Module.finrank ℂ (basis.representation label).vector ^ 2 = Nat.card G := by
  have hequal := finiteIrreducibleCharacterBasis_sum_degree_sq basis
  simp only [FiniteComplexRepresentation.character, Representation.char_one] at hequal
  exact_mod_cast hequal

theorem finiteIrreducibleCharacterBasis_exhaustion_of_degree_sum {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) {index : Type*} [Fintype index]
    (labels : index → basis.index) (hinjective : Function.Injective labels)
    (hsum : ∑ label, Module.finrank ℂ (basis.representation (labels label)).vector ^ 2 = Nat.card G) :
    Function.Surjective labels := by
  let support := Finset.univ.image labels
  have hsumSupport : (∑ label ∈ support, Module.finrank ℂ (basis.representation label).vector ^ 2) =
      Nat.card G := by
    rw [Finset.sum_image (fun left _ right _ hequal => hinjective hequal)]
    exact hsum
  have houtside : ∀ label, label ∉ support → Module.finrank ℂ (basis.representation label).vector ^ 2 = 0 := by
    intro label hnot
    have hsumComplement : (∑ member ∈ (Finset.univ : Finset basis.index) \ support,
        Module.finrank ℂ (basis.representation member).vector ^ 2) = 0 := by
      have hpartition := Finset.sum_sdiff (Finset.subset_univ support)
        (f := fun member => Module.finrank ℂ (basis.representation member).vector ^ 2)
      rw [finiteIrreducibleCharacterBasis_sum_finrank_sq basis, hsumSupport] at hpartition
      omega
    exact (Finset.sum_eq_zero_iff.mp hsumComplement) label (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
  intro label
  have hmember : label ∈ support := by
    by_contra hnot
    have hzero := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp (houtside label hnot)
    apply irreducible_character_degree_ne_zero (basis.representation label) (basis.irreducible label)
    rw [FiniteComplexRepresentation.character, Representation.char_one, hzero, Nat.cast_zero]
  obtain ⟨preimage, _, hequal⟩ := Finset.mem_image.mp hmember
  exact ⟨preimage, hequal⟩

theorem scalarHomRepresentation_norm {G : Type*} [Group G] [Fintype G]
    (homomorphism : G →* ℂ) :
    characterPairing (scalarHomRepresentation homomorphism).character
      (scalarHomRepresentation homomorphism).character = 1 := by
  rw [scalarHomRepresentation_character]
  unfold characterPairing
  simp only [← map_mul, mul_inv_cancel, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ← Nat.card_eq_fintype_card]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end CFSG.TwoRankLowerBound.Helpers
