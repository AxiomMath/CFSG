module

public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {A : Type*} [CommGroup A]

theorem sum_Irr_apply_eq_leftRegular_character [Finite A] (g : A) :
    ∑ χ ∈ irrFinset A, χ g = (Representation.leftRegular ℂ A).character g := by
  rw [leftRegular_character_eq_sum, Finset.sum_apply,
    ← Finset.sum_coe_sort (irrFinset A) fun χ : A → ℂ => χ g]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Pi.smul_apply, Irr.apply_one_eq_one (mem_irrFinset.1 χ.2), one_smul]

theorem sum_Irr_apply_of_ne_one [Finite A] {g : A} (hg : g ≠ 1) :
    ∑ χ ∈ irrFinset A, χ g = 0 := by
  rw [sum_Irr_apply_eq_leftRegular_character, leftRegular_character_of_ne_one hg]

theorem sum_Irr_apply_one [Finite A] : ∑ χ ∈ irrFinset A, χ (1 : A) = (Nat.card A : ℂ) := by
  rw [sum_Irr_apply_eq_leftRegular_character, leftRegular_character_one]

theorem sum_Irr_apply_eq_ite [Finite A] [DecidableEq A] (g : A) :
    ∑ χ ∈ irrFinset A, χ g = if g = 1 then (Nat.card A : ℂ) else 0 := by
  rw [sum_Irr_apply_eq_leftRegular_character, leftRegular_character_apply]

theorem sum_Irr_apply_eq_ite' [Finite A] [DecidableEq A] (g : A) :
    ∑ χ : irrFinset A, (χ : A → ℂ) g = if g = 1 then (Nat.card A : ℂ) else 0 := by
  rw [Finset.sum_coe_sort (irrFinset A) fun χ : A → ℂ => χ g]
  exact sum_Irr_apply_eq_ite g

theorem exists_mem_Irr_apply_ne_one [Finite A] {g : A} (hg : g ≠ 1) :
    ∃ χ ∈ Irr A, χ g ≠ 1 := by
  by_contra h
  have h1 : ∀ χ ∈ irrFinset A, χ g = 1 := fun χ hχ => by
    by_contra hne; exact h ⟨χ, mem_irrFinset.1 hχ, hne⟩
  have h0 : ∑ χ ∈ irrFinset A, χ g = 0 := sum_Irr_apply_of_ne_one hg
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one,
    card_irrFinset (A := A)] at h0
  exact (Nat.cast_ne_zero.2 Nat.card_pos.ne') h0

theorem forall_mem_Irr_apply_eq_one_iff [Finite A] {g : A} :
    (∀ χ ∈ Irr A, χ g = 1) ↔ g = 1 := by
  refine ⟨fun h => ?_, fun hg χ hχ => hg ▸ Irr.apply_one_eq_one hχ⟩
  by_contra hg
  obtain ⟨χ, hχ, hne⟩ := exists_mem_Irr_apply_ne_one hg
  exact hne (h χ hχ)

theorem exists_monoidHom_apply_ne_one [Finite A] {g : A} (hg : g ≠ 1) :
    ∃ ψ : A →* ℂˣ, (ψ g : ℂ) ≠ 1 := by
  obtain ⟨χ, hχ, hne⟩ := exists_mem_Irr_apply_ne_one hg
  obtain ⟨ψ, rfl⟩ := exists_linearCharFun_eq_of_mem_Irr hχ
  exact ⟨ψ, by simpa using hne⟩

end CFSG.FeitThompson
