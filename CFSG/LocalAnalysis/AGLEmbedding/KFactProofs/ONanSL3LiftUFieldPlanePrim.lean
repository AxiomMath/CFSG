module

public import Mathlib.Data.Nat.Prime.Defs
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

theorem exists_primitive_prime_three {p f₀ : ℕ} (hp : p.Prime) (hq₀ : 4 ≤ p ^ f₀) :
    ∃ r : ℕ, r.Prime ∧ r ∣ p ^ (2 * (3 * f₀)) - 1 ∧
      ∀ k, 0 < k → k < 2 * (3 * f₀) → ¬ r ∣ p ^ k - 1 := by
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with rfl | h
    · simp at hq₀
    · exact h
  by_cases hp2 : p = 2
  · subst hp2
    have hf₀2 : 2 ≤ f₀ := by
      by_contra hlt
      have : f₀ = 1 := by omega
      subst this
      simp at hq₀
    exact CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * (3 * f₀)) (by omega)
      (by omega)
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3 (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
