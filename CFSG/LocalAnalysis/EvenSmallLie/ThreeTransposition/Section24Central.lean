module

public import CFSG.LocalAnalysis.EvenSmallLie.ThreeTransposition.Section24

public section

namespace CFSG.EvenSmallLie.ThreeTransposition

variable {G : Type} [Group G]

theorem isThreeTranspositionSet_of_ker_eq {Q : Type} [Group Q] {D : Set G}
    (hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hD2 : ∀ x ∈ D, orderOf x = 2) {t : G}
    (ht2 : orderOf t = 2) (π : G →* Q) (hπ : π.ker = Subgroup.zpowers t)
    (hbar : ∀ a ∈ D, ∀ b ∈ D, orderOf (π a * π b) ∈ ({1, 2, 3} : Set ℕ))
    (hdt : ∀ d ∈ D, d * t ∉ D) : IsThreeTranspositionSet D := by
  refine ⟨hD2, fun g _ x hx => hDinv g x hx, fun a ha b hb => ?_⟩
  have ha2 := mul_self_of_orderOf (hD2 a ha)
  have hker : ∀ x : G, π x = 1 ↔ x = 1 ∨ x = t := fun x => by
    rw [← MonoidHom.mem_ker, hπ, mem_zpowers_iff_of_mul_self (mul_self_of_orderOf ht2)]
  have hpow : π ((a * b) ^ 2) = 1 ∨ π ((a * b) ^ 3) = 1 := by
    rw [map_pow, map_pow, map_mul, ← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one]
    rcases hbar a ha b hb with h | h | h
    · exact Or.inl (by rw [h]; exact one_dvd 2)
    · exact Or.inl (dvd_of_eq h)
    · exact Or.inr (dvd_of_eq (Set.mem_singleton_iff.1 h))
  rcases hpow with h | h
  · rcases (hker _).1 h with h' | h'
    · rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h') with h1 | h1 <;>
        simp [h1]
    ·
      refine absurd ?_ (hdt a ha)
      have e : b * a * b⁻¹ = a * t := by
        rw [← h', inv_of_orderOf (hD2 b hb), pow_two]
        calc b * a * b = a * a * (b * a * b) := by rw [ha2, one_mul]
          _ = a * (a * b * (a * b)) := by simp only [mul_assoc]
      rw [← e]
      exact hDinv b a ha
  · rcases (hker _).1 h with h' | h'
    · rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h') with h1 | h1 <;>
        simp [h1]
    ·
      refine absurd ?_ (hdt a ha)
      have e : b * a * b * (b * a)⁻¹ = a * t := by
        rw [← h', mul_inv_rev, inv_of_orderOf (hD2 a ha), inv_of_orderOf (hD2 b hb),
          show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
        calc b * a * b * (a * b) = a * a * (b * a * b * (a * b)) := by rw [ha2, one_mul]
          _ = a * (a * b * (a * b) * (a * b)) := by simp only [mul_assoc]
      rw [← e]
      exact hDinv (b * a) b hb

end CFSG.EvenSmallLie.ThreeTransposition
