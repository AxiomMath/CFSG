module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Foundations.PGroupNontrivialCenter
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Foundations.CentralExtensionNilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

universe u

open Subgroup

variable {p a : ℕ} {P : Type*} [Group P]

private theorem isNilpotent_aux {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∀ (P : Type u) [Group P] (a : ℕ), Nat.card P = p ^ a → Nat.card P ≤ n →
      Group.IsNilpotent P := by
  induction n with
  | zero =>
      intro P _ a hP hle
      exact absurd (le_antisymm hle (Nat.zero_le _)) (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  | succ n ih =>
      intro P _ a hP hle
      have hfin : Finite P :=
        Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
      rcases Nat.eq_zero_or_pos a with ha | ha
      ·
        have h1 : Nat.card P = 1 := by rw [hP, ha, pow_zero]
        have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp h1).1
        infer_instance
      ·
        obtain ⟨z, hzc, hz⟩ := exists_mem_center_orderOf_eq hp hP ha
        have hNle : zpowers z ≤ center P := zpowers_le.mpr hzc
        have : (zpowers z).Normal := normal_of_le_center hNle
        have hz1 : z ≠ 1 := fun h => hp.one_lt.ne (by rw [← hz, h, orderOf_one])
        have hbot : ⊥ < zpowers z := by
          refine bot_lt_iff_ne_bot.mpr fun h => hz1 ?_
          have hmem : z ∈ (⊥ : Subgroup P) := h ▸ mem_zpowers z
          simpa using hmem
        have hlt : Nat.card (P ⧸ zpowers z) < Nat.card P :=
          natCard_quotient_lt_natCard_of_bot_lt _ hbot
        obtain ⟨b, -, hb⟩ :=
          (Nat.dvd_prime_pow hp).mp (hP ▸ (zpowers z).card_quotient_dvd_card)
        have : Group.IsNilpotent (P ⧸ zpowers z) := ih (P ⧸ zpowers z) b hb (by omega)
        exact isNilpotent_of_isNilpotent_quotient_of_le_center hNle

theorem isNilpotent_of_natCard_eq_prime_pow (hp : p.Prime) (hP : Nat.card P = p ^ a) :
    Group.IsNilpotent P :=
  isNilpotent_aux hp (Nat.card P) P a hP le_rfl

theorem exists_central_series_of_natCard_eq_prime_pow (hp : p.Prime) (hP : Nat.card P = p ^ a) :
    ∃ (r : ℕ) (X : ℕ → Subgroup P), X 0 = ⊥ ∧ X r = ⊤ ∧ (∀ i < r, X i ≤ X (i + 1)) ∧
      (∀ i, (X i).Normal) ∧ ∀ i < r,
        Subgroup.closure {g : P | ∃ x ∈ (⊤ : Subgroup P), ∃ y ∈ X (i + 1),
          x⁻¹ * y⁻¹ * x * y = g} ≤ X i :=
  isNilpotent_iff_exists_central_series.mp (isNilpotent_of_natCard_eq_prime_pow hp hP)

end

end CFSG.FeitThompson
