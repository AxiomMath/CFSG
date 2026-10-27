module

public import Mathlib.GroupTheory.Perm.Sign
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6PermK

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

theorem s6_factA : ∀ i j : Fin 5, i ≠ j → ∀ ρ a : Equiv.Perm (Fin 5), ρ ^ 3 = 1 → ρ ≠ 1 →
    ρ * Equiv.swap i j = Equiv.swap i j * ρ → a * Equiv.swap i j = Equiv.swap i j * a →
    (a * ρ * a⁻¹ * ρ⁻¹) ^ 3 = 1 ∧ (a * ρ = ρ * a → a ^ 12 = 1 ∧
      (a ^ 4 = 1 → a = 1 ∨ a = Equiv.swap i j)) :=
  fun i j hij ρ a h3 h1 hc ha => S6PermK.factA i j hij ρ a h3 h1 hc ha

theorem s6_exists_rho : ∀ i j : Fin 5, i ≠ j → ∃ ρ : Equiv.Perm (Fin 5), ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧
    ρ * Equiv.swap i j = Equiv.swap i j * ρ := by
  decide +kernel

theorem s6_cent3_card : ∀ c : Equiv.Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    (Finset.univ.filter (fun p : Equiv.Perm (Fin 5) => p * c = c * p)).card = 6 :=
  fun c h3 h1 => S6PermK.cent3_card c h3 h1

theorem s6_cent3_comm : ∀ c : Equiv.Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    ∀ p q : Equiv.Perm (Fin 5), p * c = c * p → q * c = c * q → p * q = q * p :=
  fun c h3 h1 p q hp hq => S6PermK.cent3_comm c h3 h1 p q hp hq

theorem s6_sign_of_pow_three {ρ : Equiv.Perm (Fin 5)} (h : ρ ^ 3 = 1) : Equiv.Perm.sign ρ = 1 := by
  have h1 := congrArg Equiv.Perm.sign h
  rw [map_pow, map_one] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h2 | h2
  · exact h2
  · rw [h2] at h1
    exact absurd h1 (by decide)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
