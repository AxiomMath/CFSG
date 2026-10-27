module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Wreathed.FlatRelative

theorem sign_mul_pos_eq {γ γ' x x' : ℤ} (hγ : γ = 1 ∨ γ = -1) (hγ' : γ' = 1 ∨ γ' = -1)
    (hx : 0 < x) (hx' : 0 < x') (h : γ * x = γ' * x') : γ = γ' ∧ x = x' := by
  rcases hγ with rfl | rfl <;> rcases hγ' with rfl | rfl <;> constructor <;> linarith

theorem sign_mul_sign {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

theorem flat_c_eq_of_weighted {q ε t a₀ b₀ c₀ : ℤ} (hq : 3 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (ht : t ≠ 0) (ha : a₀ ≠ 0)
    (h1 : a₀ * b₀ * c₀ + q ^ 2 * t * b₀ * c₀ - (2 + ε * q) ^ 2 * t * a₀ * c₀ +
      (1 + 2 * ε * q) ^ 2 * t * a₀ * b₀ = 0)
    (h2 : -(a₀ * b₀ * c₀) - q ^ 2 * t * b₀ * c₀ + (2 * q ^ 2 - (2 + ε * q) ^ 2) * t * a₀ * c₀ +
      ((1 + 2 * ε * q) ^ 2 - 2) * t * a₀ * b₀ = 0) :
    c₀ = ε * q * b₀ := by
  have hsum : t * a₀ * ((1 + ε * q) * (ε * q * b₀ - c₀)) = 0 := by
    have h : 8 * (t * a₀ * ((1 + ε * q) * (ε * q * b₀ - c₀))) = 0 := by
      rcases hε with rfl | rfl <;> linear_combination h1 + h2
    linarith
  have hne : 1 + ε * q ≠ 0 := by rcases hε with rfl | rfl <;> omega
  have hta : t * a₀ ≠ 0 := mul_ne_zero ht ha
  have h := (mul_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left hta)).resolve_left hne
  linarith

theorem flat_quadratic_of_weighted {q ε t a₀ b₀ : ℤ} (hε : ε = 1 ∨ ε = -1) (hb : b₀ ≠ 0)
    (hY : t + a₀ - b₀ + ε * q * b₀ = 0)
    (h1 : a₀ * b₀ * (ε * q * b₀) + q ^ 2 * t * b₀ * (ε * q * b₀) -
      (2 + ε * q) ^ 2 * t * a₀ * (ε * q * b₀) + (1 + 2 * ε * q) ^ 2 * t * a₀ * b₀ = 0) :
    (q * a₀ + ε * t) * (a₀ + ε * q ^ 3 * t) = 0 := by
  have h1' : ε * q * b₀ * (a₀ + q ^ 2 * t) + t * a₀ * (1 - ε * q ^ 3) = 0 := by
    have h : b₀ * (ε * q * b₀ * (a₀ + q ^ 2 * t) + t * a₀ * (1 - ε * q ^ 3)) = 0 := by
      rcases hε with rfl | rfl <;> linear_combination h1
    exact (mul_eq_zero.mp h).resolve_left hb
  have hb' : b₀ * (1 - ε * q) = a₀ + t := by linarith
  have key : ε * q * (a₀ + t) * (a₀ + q ^ 2 * t) + t * a₀ * (1 - ε * q ^ 3) * (1 - ε * q) = 0 := by
    linear_combination (1 - ε * q) * h1' - ε * q * (a₀ + q ^ 2 * t) * hb'
  rcases hε with rfl | rfl
  · linear_combination key
  · linear_combination -key

theorem flat_alternatives {q ε : ℤ} (hq : 3 ≤ q) (hε : ε = 1 ∨ ε = -1)
    {f₀ f₁ f₂ f₃ f₄ D Δ : ℤ} (hf₀ : 0 < f₀) (hf₁ : 0 < f₁) (hf₂ : 0 < f₂) (hf₃ : 0 < f₃)
    (hf₄ : 0 < f₄) (hD : 0 < D) (hΔ : 0 < Δ) {δ₀ δ₁ δ₂ δ₃ δ₄ α γ : ℤ}
    (s₀ : δ₀ = 1 ∨ δ₀ = -1) (s₁ : δ₁ = 1 ∨ δ₁ = -1) (s₂ : δ₂ = 1 ∨ δ₂ = -1)
    (s₃ : δ₃ = 1 ∨ δ₃ = -1) (s₄ : δ₄ = 1 ∨ δ₄ = -1) (sα : α = 1 ∨ α = -1)
    (sγ : γ = 1 ∨ γ = -1)
    (hlin1 : δ₀ * f₀ + δ₁ * f₁ = -(α * D)) (hlin2 : δ₂ * f₂ + δ₃ * f₃ = -(α * D))
    (h4 : δ₄ * f₄ = δ₃ * f₃ - δ₀ * f₀) (hgΔ : γ * Δ = δ₂ * f₂ - δ₃ * f₃)
    (h1 : δ₀ * f₀ * (δ₂ * f₂) * -(δ₃ * f₃) + q ^ 2 * (δ₁ * f₁) * (δ₂ * f₂) * -(δ₃ * f₃) -
      (2 + ε * q) ^ 2 * (δ₁ * f₁) * (δ₀ * f₀) * -(δ₃ * f₃) +
      (1 + 2 * ε * q) ^ 2 * (δ₁ * f₁) * (δ₀ * f₀) * (δ₂ * f₂) = 0)
    (h2 : -(δ₀ * f₀ * (δ₂ * f₂) * -(δ₃ * f₃)) - q ^ 2 * (δ₁ * f₁) * (δ₂ * f₂) * -(δ₃ * f₃) +
      (2 * q ^ 2 - (2 + ε * q) ^ 2) * (δ₁ * f₁) * (δ₀ * f₀) * -(δ₃ * f₃) +
      ((1 + 2 * ε * q) ^ 2 - 2) * (δ₁ * f₁) * (δ₀ * f₀) * (δ₂ * f₂) = 0) :
    (f₀ = q ^ 3 * f₁ ∧ f₂ = (q ^ 2 + ε * q + 1) * f₁ ∧ f₃ = q * (q ^ 2 + ε * q + 1) * f₁ ∧
      f₄ = q * (q + ε) * f₁ ∧ δ₀ = -(ε * δ₁) ∧ δ₂ = δ₁ ∧ δ₃ = -(ε * δ₁) ∧ δ₄ = -δ₁ ∧
      α = ε * δ₁ ∧ γ = ε * δ₁ ∧ D = (q ^ 3 - ε) * f₁ ∧
      Δ = (q + ε) * (q ^ 2 + ε * q + 1) * f₁) ∨
    (q ∣ f₁ ∧ q * f₀ = f₁ ∧ q * f₂ = f₁ ∧ f₃ = f₁ ∧ q * f₄ = (q + ε) * f₁ ∧
      δ₀ = -(ε * δ₁) ∧ δ₂ = -(ε * δ₁) ∧ δ₃ = δ₁ ∧ δ₄ = δ₁ ∧ α = -δ₁ ∧ γ = -δ₁ ∧
      q * D = (q - ε) * f₁ ∧ q * Δ = (q + ε) * f₁) := by
  have hne : ∀ {δ f : ℤ}, (δ = 1 ∨ δ = -1) → 0 < f → δ * f ≠ 0 := fun hδ hf => by
    rcases hδ with rfl | rfl <;> omega
  have ht := hne s₁ hf₁
  have ha := hne s₀ hf₀
  have hb := hne s₂ hf₂
  have hY : δ₁ * f₁ + δ₀ * f₀ - δ₂ * f₂ + -(δ₃ * f₃) = 0 := by linarith
  have hc := flat_c_eq_of_weighted hq hε ht ha h1 h2
  rw [hc] at h1 hY
  have hquad := flat_quadratic_of_weighted hε hb hY h1
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hs₁ : δ₁ * δ₁ = 1 := by rcases s₁ with rfl | rfl <;> norm_num
  have hεδ := sign_mul_sign hε s₁
  have hnεδ : -(ε * δ₁) = 1 ∨ -(ε * δ₁) = -1 := by
    rcases hεδ with h | h <;> rw [h] <;> norm_num
  have hnδ : -δ₁ = 1 ∨ -δ₁ = -1 := by rcases s₁ with h | h <;> rw [h] <;> norm_num
  have hqε : 0 < q + ε := by rcases hε with rfl | rfl <;> omega
  have hqε' : 0 < q - ε := by rcases hε with rfl | rfl <;> omega
  have hQ : 0 < q ^ 2 + ε * q + 1 := by rcases hε with rfl | rfl <;> nlinarith
  have hq3 : 0 < q ^ 3 - ε := by rcases hε with rfl | rfl <;> nlinarith
  have E : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h : -(δ₃ * f₃) = ε * q * (δ₂ * f₂) := hc
  rcases mul_eq_zero.mp hquad with hR | hC
  ·
    right
    obtain ⟨e₀, d₀⟩ := sign_mul_pos_eq s₀ hnεδ (by positivity) hf₁
      (show δ₀ * (q * f₀) = -(ε * δ₁) * f₁ by linear_combination hR)
    have hqb : q * (δ₂ * f₂) = -(ε * (δ₁ * f₁)) := by
      have h' : (q - ε) * (q * (δ₂ * f₂) + ε * (δ₁ * f₁)) = 0 := by
        linear_combination ε * q * hY - ε * hR - q ^ 2 * (δ₂ * f₂) * E
      have := (mul_eq_zero.mp h').resolve_left hqε'.ne'
      linarith
    obtain ⟨e₂, d₂⟩ := sign_mul_pos_eq s₂ hnεδ (by positivity) hf₁
      (show δ₂ * (q * f₂) = -(ε * δ₁) * f₁ by linear_combination hqb)
    have e3' : δ₃ * f₃ = δ₁ * f₁ := by
      linear_combination -h - ε * hqb + (δ₁ * f₁) * E
    obtain ⟨e₃, d₃⟩ := sign_mul_pos_eq s₃ s₁ hf₃ hf₁ e3'
    obtain ⟨e₄, d₄⟩ := sign_mul_pos_eq s₄ s₁ (by positivity) (by positivity)
      (show δ₄ * (q * f₄) = δ₁ * ((q + ε) * f₁) by linear_combination q * h4 + q * e3' - hR)
    obtain ⟨eα, dα⟩ := sign_mul_pos_eq sα hnδ (by positivity) (by positivity)
      (show α * (q * D) = -δ₁ * ((q - ε) * f₁) by linear_combination q * hlin1 - hR)
    obtain ⟨eγ, dγ⟩ := sign_mul_pos_eq sγ hnδ (by positivity) (by positivity)
      (show γ * (q * Δ) = -δ₁ * ((q + ε) * f₁) by linear_combination q * hgΔ + hqb - q * e3')
    exact ⟨⟨f₀, d₀.symm⟩, d₀, d₂, d₃, d₄, e₀, e₂, e₃, e₄, eα, eγ, dα, dγ⟩
  ·
    left
    obtain ⟨e₀, d₀⟩ := sign_mul_pos_eq s₀ hnεδ hf₀ (by positivity)
      (show δ₀ * f₀ = -(ε * δ₁) * (q ^ 3 * f₁) by linear_combination hC)
    have hb₀ : δ₂ * f₂ = δ₁ * ((q ^ 2 + ε * q + 1) * f₁) := by
      have hne1 : 1 - ε * q ≠ 0 := by rcases hε with rfl | rfl <;> omega
      have h' : (1 - ε * q) * (δ₂ * f₂ - δ₁ * ((q ^ 2 + ε * q + 1) * f₁)) = 0 := by
        linear_combination -hY + hC + q ^ 2 * (δ₁ * f₁) * E
      have := (mul_eq_zero.mp h').resolve_left hne1
      linarith
    obtain ⟨e₂, d₂⟩ := sign_mul_pos_eq s₂ s₁ hf₂ (by positivity) hb₀
    have e3c : δ₃ * f₃ = -(ε * δ₁) * (q * (q ^ 2 + ε * q + 1) * f₁) := by
      linear_combination -h - ε * q * hb₀
    obtain ⟨e₃, d₃⟩ := sign_mul_pos_eq s₃ hnεδ hf₃ (by positivity) e3c
    obtain ⟨e₄, d₄⟩ := sign_mul_pos_eq s₄ hnδ hf₄ (by positivity)
      (show δ₄ * f₄ = -δ₁ * (q * (q + ε) * f₁) by
        linear_combination h4 + e3c - hC - q ^ 2 * (δ₁ * f₁) * E)
    obtain ⟨eα, dα⟩ := sign_mul_pos_eq sα hεδ hD (by positivity)
      (show α * D = ε * δ₁ * ((q ^ 3 - ε) * f₁) by
        linear_combination hlin1 - hC + (δ₁ * f₁) * E)
    obtain ⟨eγ, dγ⟩ := sign_mul_pos_eq sγ hεδ hΔ (by positivity)
      (show γ * Δ = ε * δ₁ * ((q + ε) * (q ^ 2 + ε * q + 1) * f₁) by
        linear_combination hgΔ + hb₀ - e3c - (q ^ 2 + ε * q + 1) * (δ₁ * f₁) * E)
    exact ⟨d₀, d₂, d₃, d₄, e₀, e₂, e₃, e₄, eα, eγ, dα, dγ⟩

end CFSG.Wreathed.FlatRelative
