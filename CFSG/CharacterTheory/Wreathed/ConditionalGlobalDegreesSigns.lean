module

public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesSolve
public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesClass

public section

namespace CFSG.Wreathed.ConditionalGlobalDegrees

theorem signs_of_weighted {q ε σ τ₀ κ dA dB dD : ℤ} (hq : 3 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ₀ = 1 ∨ τ₀ = -1) (hκ : κ = 1 ∨ κ = -1)
    (hA : 0 < dA) (hB : 0 < dB) (hD : 0 < dD) (hY : 1 + σ * dA - τ₀ * dB + κ * dD = 0)
    (hWY : (1 : ℂ) + σ * ((q : ℂ) ^ 2 / dA) - τ₀ * ((2 + ε * q) ^ 2 / dB) +
      κ * ((1 + 2 * ε * q) ^ 2 / dD) = 0)
    (hWX : -(1 : ℂ) - σ * ((q : ℂ) ^ 2 / dA) - τ₀ * ((2 + ε * q) ^ 2 / dB) +
      κ * ((1 + 2 * ε * q) ^ 2 / dD) + τ₀ * ((q : ℂ) ^ 2 / dB + (q : ℂ) ^ 2 / dB) -
      κ * (1 / dD + 1 / dD) = 0) :
    σ = -ε ∧ τ₀ = 1 ∧ κ = ε ∧ dA = q ^ 3 ∧ dB = q ^ 2 + ε * q + 1 ∧
      dD = q * (q ^ 2 + ε * q + 1) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hτ2 : τ₀ * τ₀ = 1 := by rcases hτ with h | h <;> rw [h] <;> norm_num
  have hκ2 : κ * κ = 1 := by rcases hκ with h | h <;> rw [h] <;> norm_num
  have E1 := weighted_eq_int hA.ne' hB.ne' hD.ne' (c₀ := 1) (cA := σ) (nA := q ^ 2)
    (cB := -τ₀) (nB := (2 + ε * q) ^ 2) (cD := κ) (nD := (1 + 2 * ε * q) ^ 2)
    (by push_cast; linear_combination hWY)
  have E2 := weighted_eq_int hA.ne' hB.ne' hD.ne' (c₀ := -1) (cA := -σ) (nA := q ^ 2)
    (cB := τ₀) (nB := 2 * q ^ 2 - (2 + ε * q) ^ 2) (cD := κ)
    (nD := (1 + 2 * ε * q) ^ 2 - 2) (by push_cast; linear_combination hWX)
  have h1 : σ * dA * (τ₀ * dB) * (κ * dD) + q ^ 2 * (τ₀ * dB) * (κ * dD) -
      (2 + ε * q) ^ 2 * (σ * dA) * (κ * dD) + (1 + 2 * ε * q) ^ 2 * (σ * dA) * (τ₀ * dB) = 0 := by
    linear_combination (σ * τ₀ * κ) * E1 - q ^ 2 * τ₀ * κ * dB * dD * hσ2 +
      (2 + ε * q) ^ 2 * σ * κ * dA * dD * hτ2 - (1 + 2 * ε * q) ^ 2 * σ * τ₀ * dA * dB * hκ2
  have h2 : -(σ * dA * (τ₀ * dB) * (κ * dD)) - q ^ 2 * (τ₀ * dB) * (κ * dD) +
      (2 * q ^ 2 - (2 + ε * q) ^ 2) * (σ * dA) * (κ * dD) +
      ((1 + 2 * ε * q) ^ 2 - 2) * (σ * dA) * (τ₀ * dB) = 0 := by
    linear_combination (σ * τ₀ * κ) * E2 + q ^ 2 * τ₀ * κ * dB * dD * hσ2 -
      (2 * q ^ 2 - (2 + ε * q) ^ 2) * σ * κ * dA * dD * hτ2 -
      ((1 + 2 * ε * q) ^ 2 - 2) * σ * τ₀ * dA * dB * hκ2
  have ha : σ * dA ≠ 0 := mul_ne_zero (by rcases hσ with h | h <;> rw [h] <;> norm_num) hA.ne'
  have hb : τ₀ * dB ≠ 0 := mul_ne_zero (by rcases hτ with h | h <;> rw [h] <;> norm_num) hB.ne'
  have hY' : 1 + σ * dA - τ₀ * dB + κ * dD = 0 := hY
  obtain ⟨ha₀, hb₀, hc₀⟩ := global_degrees_solve hq hε ha hb hY' h1 h2
  have hq3 : 0 < q ^ 3 := by positivity
  have hQd : 0 < q ^ 2 + ε * q + 1 := by rcases hε with h | h <;> rw [h] <;> nlinarith
  have hqQ : 0 < q * (q ^ 2 + ε * q + 1) := mul_pos (by omega) hQd
  have hσε : σ = -ε := by
    rcases hσ with rfl | rfl <;> rcases hε with rfl | rfl <;> omega
  have hτ1 : τ₀ = 1 := by
    rcases hτ with h | h
    · exact h
    · exfalso
      rw [h] at hb₀
      linarith
  have hκε : κ = ε := by
    rcases hκ with rfl | rfl <;> rcases hε with rfl | rfl <;>
      first | omega | (exfalso; linarith)
  refine ⟨hσε, hτ1, hκε, ?_, ?_, ?_⟩
  · rw [hσε] at ha₀
    rcases hε with h | h <;> rw [h] at ha₀ <;> linarith
  · rw [hτ1] at hb₀
    linarith
  · rw [hκε] at hc₀
    rcases hε with h | h <;> rw [h] at hc₀ ⊢ <;> linarith

end CFSG.Wreathed.ConditionalGlobalDegrees
