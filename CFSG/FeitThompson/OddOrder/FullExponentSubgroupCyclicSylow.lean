module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup
import CFSG.FeitThompson.Foundations.SylowExponentPrimePart

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {E : Type*} [Group E] [Finite E]

theorem exponent_eq_natCard_of_isCyclic_of_natCard_eq_pow_factorization
    (hE : ∀ p : ℕ, p.Prime → ∀ P : Subgroup E,
      Nat.card P = p ^ (Nat.card E).factorization p → IsCyclic P) :
    Monoid.exponent E = Nat.card E := by
  refine Nat.eq_of_factorization_eq (Monoid.ExponentExists.exponent_ne_zero .of_finite)
    Nat.card_pos.ne' fun p => ?_
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p E))
    have hcard : Nat.card (P : Subgroup E) = p ^ (Nat.card E).factorization p :=
      P.card_eq_multiplicity
    have hcyc := hE p hp _ hcard
    have h₁ : Monoid.exponent (P : Subgroup E) = p ^ (Monoid.exponent E).factorization p :=
      exponent_eq_pow_factorization_exponent hp hcard
    have h₂ : Monoid.exponent (P : Subgroup E) = p ^ (Nat.card E).factorization p := by
      rw [IsCyclic.exponent_eq_card, hcard]
    exact Nat.pow_right_injective hp.two_le (h₁.symm.trans h₂)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem natCard_eq_of_exponent_eq_of_isCyclic_of_natCard_eq_pow_factorization
    (hE : ∀ p : ℕ, p.Prime → ∀ P : Subgroup E,
      Nat.card P = p ^ (Nat.card E).factorization p → IsCyclic P) {E₀ : Subgroup E}
    (h₀ : Monoid.exponent E₀ = Monoid.exponent E) : Nat.card E₀ = Nat.card E :=
  Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card E₀) <| by
    rw [← exponent_eq_natCard_of_isCyclic_of_natCard_eq_pow_factorization hE, ← h₀]
    exact Group.exponent_dvd_nat_card

theorem exponent_eq_natCard_and_eq_top_of_exponent_eq
    (hE : ∀ p : ℕ, p.Prime → ∀ P : Subgroup E,
      Nat.card P = p ^ (Nat.card E).factorization p → IsCyclic P) {E₀ : Subgroup E}
    (h₀ : Monoid.exponent E₀ = Monoid.exponent E) :
    Monoid.exponent E = Nat.card E ∧ E₀ = ⊤ :=
  ⟨exponent_eq_natCard_of_isCyclic_of_natCard_eq_pow_factorization hE,
    Subgroup.eq_top_of_card_eq _
      (natCard_eq_of_exponent_eq_of_isCyclic_of_natCard_eq_pow_factorization hE h₀)⟩

theorem exponent_eq_natCard_and_eq_top_of_exponent_eq_of_isZGroup [IsZGroup E] {E₀ : Subgroup E}
    (h₀ : Monoid.exponent E₀ = Monoid.exponent E) :
    Monoid.exponent E = Nat.card E ∧ E₀ = ⊤ :=
  exponent_eq_natCard_and_eq_top_of_exponent_eq
    (fun p hp P hP => by
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨Q, hQ⟩ : ∃ Q : Sylow p E, (Q : Subgroup E) = P := ⟨Sylow.ofCard P hP, rfl⟩
      exact hQ ▸ IsZGroup.isZGroup p hp Q) h₀

theorem eq_top_of_exponent_eq_of_isZGroup [IsZGroup E] {E₀ : Subgroup E}
    (h₀ : Monoid.exponent E₀ = Monoid.exponent E) : E₀ = ⊤ :=
  (exponent_eq_natCard_and_eq_top_of_exponent_eq_of_isZGroup h₀).2

end

end CFSG.FeitThompson
