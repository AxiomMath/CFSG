module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Wreathed.ConditionalGlobalDegrees

theorem c_eq_of_weighted {q ε a₀ b₀ c₀ : ℤ} (hq : 3 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (ha : a₀ ≠ 0)
    (h1 : a₀ * b₀ * c₀ + q ^ 2 * b₀ * c₀ - (2 + ε * q) ^ 2 * a₀ * c₀ +
      (1 + 2 * ε * q) ^ 2 * a₀ * b₀ = 0)
    (h2 : -(a₀ * b₀ * c₀) - q ^ 2 * b₀ * c₀ + (2 * q ^ 2 - (2 + ε * q) ^ 2) * a₀ * c₀ +
      ((1 + 2 * ε * q) ^ 2 - 2) * a₀ * b₀ = 0) :
    c₀ = ε * q * b₀ := by
  have hsum : a₀ * ((1 + ε * q) * (ε * q * b₀ - c₀)) = 0 := by
    have h : 8 * (a₀ * ((1 + ε * q) * (ε * q * b₀ - c₀))) = 0 := by
      rcases hε with rfl | rfl <;> linear_combination h1 + h2
    linarith
  have hne : 1 + ε * q ≠ 0 := by rcases hε with rfl | rfl <;> omega
  have h := (mul_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left ha)).resolve_left hne
  linarith

theorem quadratic_of_weighted {q ε a₀ b₀ : ℤ} (hε : ε = 1 ∨ ε = -1) (hb : b₀ ≠ 0)
    (hY : 1 + a₀ - b₀ + ε * q * b₀ = 0)
    (h1 : a₀ * b₀ * (ε * q * b₀) + q ^ 2 * b₀ * (ε * q * b₀) -
      (2 + ε * q) ^ 2 * a₀ * (ε * q * b₀) + (1 + 2 * ε * q) ^ 2 * a₀ * b₀ = 0) :
    (q * a₀ + ε) * (a₀ + ε * q ^ 3) = 0 := by
  have h1' : ε * q * b₀ * (a₀ + q ^ 2) + a₀ * (1 - ε * q ^ 3) = 0 := by
    have h : b₀ * (ε * q * b₀ * (a₀ + q ^ 2) + a₀ * (1 - ε * q ^ 3)) = 0 := by
      rcases hε with rfl | rfl <;> linear_combination h1
    exact (mul_eq_zero.mp h).resolve_left hb
  have hb' : b₀ * (1 - ε * q) = a₀ + 1 := by linarith
  have key : ε * q * (a₀ + 1) * (a₀ + q ^ 2) + a₀ * (1 - ε * q ^ 3) * (1 - ε * q) = 0 := by
    linear_combination (1 - ε * q) * h1' - ε * q * (a₀ + q ^ 2) * hb'
  rcases hε with rfl | rfl
  · linear_combination key
  · linear_combination -key

theorem global_degrees_solve {q ε a₀ b₀ c₀ : ℤ} (hq : 3 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (ha : a₀ ≠ 0) (hb : b₀ ≠ 0) (hY : 1 + a₀ - b₀ + c₀ = 0)
    (h1 : a₀ * b₀ * c₀ + q ^ 2 * b₀ * c₀ - (2 + ε * q) ^ 2 * a₀ * c₀ +
      (1 + 2 * ε * q) ^ 2 * a₀ * b₀ = 0)
    (h2 : -(a₀ * b₀ * c₀) - q ^ 2 * b₀ * c₀ + (2 * q ^ 2 - (2 + ε * q) ^ 2) * a₀ * c₀ +
      ((1 + 2 * ε * q) ^ 2 - 2) * a₀ * b₀ = 0) :
    a₀ = -ε * q ^ 3 ∧ b₀ = q ^ 2 + ε * q + 1 ∧ c₀ = ε * q * (q ^ 2 + ε * q + 1) := by
  have hc := c_eq_of_weighted hq hε ha h1 h2
  subst hc
  have hquad := quadratic_of_weighted hε hb hY h1
  have ha₀ : a₀ = -ε * q ^ 3 := by
    rcases mul_eq_zero.mp hquad with h | h
    · exfalso
      have hdvd : q ∣ 1 := by
        rcases hε with rfl | rfl
        · exact ⟨-a₀, by linarith⟩
        · exact ⟨a₀, by linarith⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
    · linarith
  have hne : 1 - ε * q ≠ 0 := by rcases hε with rfl | rfl <;> omega
  have hb₀ : b₀ = q ^ 2 + ε * q + 1 := by
    have h : (1 - ε * q) * (b₀ - (q ^ 2 + ε * q + 1)) = 0 := by
      rw [ha₀] at hY
      rcases hε with rfl | rfl <;> linear_combination -hY
    have := (mul_eq_zero.mp h).resolve_left hne
    linarith
  exact ⟨ha₀, hb₀, by rw [hb₀]⟩

end CFSG.Wreathed.ConditionalGlobalDegrees
