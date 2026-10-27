module

public import CFSG.Quasithin.Background.Module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin

variable {S : Type} [CommGroup S] [Finite S] {G : Subgroup (MulAut S)}

omit [Finite S] in
theorem exists_minimal_offender {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) :
    ∃ A₀ : Subgroup (MulAut S), IsFFStarOffender G A₀ ∧
      ∀ B : Subgroup (MulAut S), IsFFStarOffender G B → Nat.card A₀ ≤ Nat.card B := by
  classical
  have hex : ∃ n : ℕ, ∃ B : Subgroup (MulAut S), IsFFStarOffender G B ∧ Nat.card B = n :=
    ⟨_, A, hA, rfl⟩
  obtain ⟨B₀, hB₀, hn⟩ := Nat.find_spec hex
  refine ⟨B₀, hB₀, fun B hB => ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨B, hB, rfl⟩

theorem card_lt_of_proper {A₀ : Subgroup (MulAut S)} (h : IsFFStarOffender G A₀)
    (hmin : ∀ B : Subgroup (MulAut S), IsFFStarOffender G B → Nat.card A₀ ≤ Nat.card B)
    {B : Subgroup (MulAut S)} (hBle : B ≤ A₀) (hB1 : B ≠ ⊥) (hBne : B ≠ A₀) :
    Nat.card B * Nat.card (fixV B) < Nat.card A₀ * Nat.card (fixV A₀) := by
  have hle := h.2.2.2 B hBle
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hoff : IsFFStarOffender G B := by
      refine ⟨hBle.trans h.1, hB1, ⟨fun a ha b hb => h.2.2.1.1 a (hBle ha) b (hBle hb),
        fun a ha => h.2.2.1.2 a (hBle ha)⟩, fun B' hB' => ?_⟩
      rw [heq]
      exact h.2.2.2 B' (hB'.trans hBle)
    have h1 := hmin B hoff
    have h2 : Nat.card B < Nat.card A₀ := by
      apply lt_of_le_of_ne (Subgroup.card_le_of_le hBle)
      intro hc
      exact hBne (Subgroup.eq_of_le_of_card_ge hBle (le_of_eq hc.symm))
    omega

theorem fixV_eq_of_maximal {A₀ : Subgroup (MulAut S)} (h : IsFFStarOffender G A₀)
    (hmin : ∀ B : Subgroup (MulAut S), IsFFStarOffender G B → Nat.card A₀ ≤ Nat.card B)
    {B : Subgroup (MulAut S)} (hBle : B ≤ A₀) (hB1 : B ≠ ⊥) (hcard : Nat.card A₀ = 2 * Nat.card B) :
    fixV B = fixV A₀ := by
  have hBne : B ≠ A₀ := by
    intro hB
    subst hB
    have : 0 < Nat.card B := Nat.card_pos
    omega
  have hlt := card_lt_of_proper h hmin hBle hB1 hBne
  have hsub : fixV A₀ ≤ fixV B := fun v hv b hb => hv b (hBle hb)
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hc : Nat.card (fixV B) ≤ Nat.card (fixV A₀) := by
    have h1 : Nat.card B * Nat.card (fixV B) < 2 * Nat.card B * Nat.card (fixV A₀) := by
      rw [hcard] at hlt
      linarith
    have h2 : Nat.card (fixV B) < 2 * Nat.card (fixV A₀) := by
      by_contra hcon
      push Not at hcon
      have := Nat.mul_le_mul_left (Nat.card B) hcon
      nlinarith
    have hdvd : Nat.card (fixV A₀) ∣ Nat.card (fixV B) := by
      have := Subgroup.card_dvd_of_le hsub
      exact this
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : k < 2 := by
      by_contra hcon
      push Not at hcon
      have hpos' : 0 < Nat.card (fixV A₀) := Nat.card_pos
      have : 2 * Nat.card (fixV A₀) ≤ Nat.card (fixV A₀) * k := by nlinarith
      omega
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso
        have : 0 < Nat.card (fixV B) := Nat.card_pos
        rw [hk, h0] at this
        simp at this
      · exact h0
    have : k = 1 := by omega
    rw [hk, this, mul_one]
  exact (Subgroup.eq_of_le_of_card_ge hsub hc).symm

end CFSG.QuasithinUnique.B42A57
