module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FieldSimp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

variable {K : Type*} [Field K]

theorem fixed_of_quadratic_roots {ρ : K ≃+* K} (hρ3 : ∀ x, ρ (ρ (ρ x)) = x) {r ε ν : K}
    (hε : ρ ε = ε) (hν : ρ ν = ν) (h : r ^ 2 + ε * r = ν) : ρ r = r := by
  have h1 : ρ r ^ 2 + ε * ρ r = ν := by
    have := congrArg ρ h
    simpa [map_add, map_mul, map_pow, hε, hν] using this
  have h2 : ρ (ρ r) ^ 2 + ε * ρ (ρ r) = ν := by
    have := congrArg ρ h1
    simpa [map_add, map_mul, map_pow, hε, hν] using this
  by_contra hne
  have e1 : r + ρ r + ε = 0 := by
    have : (r - ρ r) * (r + ρ r + ε) = 0 := by linear_combination h - h1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  have hne2 : ρ r ≠ ρ (ρ r) := fun h' => hne (ρ.injective h').symm
  have e2 : ρ r + ρ (ρ r) + ε = 0 := by
    have : (ρ r - ρ (ρ r)) * (ρ r + ρ (ρ r) + ε) = 0 := by linear_combination h1 - h2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne2)
  have e3 : ρ (ρ r) = r := by linear_combination e2 - e1
  apply hne
  have := congrArg ρ e3
  rw [hρ3] at this
  exact this.symm

variable {ι ρ : K ≃+* K}

theorem ratio_fixed_of_norms (hι : ∀ x, ι (ι x) = x) (hρ3 : ∀ x, ρ (ρ (ρ x)) = x)
    {c r₂ : K} (hc : ρ c = c) (hcι : ι c = -c) (hc0 : c ≠ 0) (hr : ρ r₂ = r₂)
    (hrι : ι r₂ = r₂) (hr0 : r₂ ≠ 0) (hr1 : r₂ ≠ 1) {x y : K}
    (h0 : ρ (ι x * x) = ι x * x)
    (h1 : ρ (ι (x + c * y) * (x + c * y)) = ι (x + c * y) * (x + c * y))
    (h2 : ρ (ι (x + c * r₂ * y) * (x + c * r₂ * y)) = ι (x + c * r₂ * y) * (x + c * r₂ * y))
    (hy : y ≠ 0) : ρ (x / y) = x / y := by
  set A := ι x * x with hA
  set δ := ι x * y - ι y * x with hδ
  set Ny := ι y * y with hNy
  have e1 : ι (x + c * y) * (x + c * y) = A + c * δ - c ^ 2 * Ny := by
    rw [map_add, map_mul, hcι]
    simp only [hA, hδ, hNy]
    ring
  have e2 : ι (x + c * r₂ * y) * (x + c * r₂ * y) = A + c * r₂ * δ - c ^ 2 * r₂ ^ 2 * Ny := by
    rw [map_add, map_mul, map_mul, hcι, hrι]
    simp only [hA, hδ, hNy]
    ring
  rw [e1] at h1
  rw [e2] at h2
  simp only [map_add, map_sub, map_mul, map_pow, hc, hr, h0] at h1 h2
  have hS1 : c * (ρ δ - δ) = c ^ 2 * (ρ Ny - Ny) := by linear_combination h1 - (1 - 1) * h0
  have hS2 : c * r₂ * (ρ δ - δ) = c ^ 2 * r₂ ^ 2 * (ρ Ny - Ny) := by
    linear_combination h2 - (1 - 1) * h0
  have hD : ρ δ - δ = c * (ρ Ny - Ny) := by
    apply mul_left_cancel₀ hc0
    linear_combination hS1
  have hS : ρ Ny - Ny = 0 := by
    have : c * r₂ * (c * (ρ Ny - Ny)) = c ^ 2 * r₂ ^ 2 * (ρ Ny - Ny) := by
      rw [← hD]; exact hS2
    have h3 : c ^ 2 * r₂ * (1 - r₂) * (ρ Ny - Ny) = 0 := by linear_combination this
    have hne : c ^ 2 * r₂ * (1 - r₂) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hc0) hr0) (sub_ne_zero.mpr (Ne.symm hr1))
    exact (mul_eq_zero.mp h3).resolve_left hne
  have hNyρ : ρ Ny = Ny := sub_eq_zero.mp hS
  have hδρ : ρ δ = δ := by
    have : ρ δ - δ = 0 := by rw [hD, hS, mul_zero]
    exact sub_eq_zero.mp this
  have hιy : ι y ≠ 0 := by
    intro h
    apply hy
    rw [← hι y, h, map_zero]
  have hNy0 : Ny ≠ 0 := mul_ne_zero hιy hy
  set r := x / y with hr'
  have hxr : x = r * y := by rw [hr']; field_simp
  have hιr : ι r = ι x / ι y := by rw [hr', map_div₀]
  have hεdef : ι r - r = δ / Ny := by
    rw [hιr, hr', hδ, hNy]
    field_simp
  have hνdef : ι r * r = A / Ny := by
    rw [hιr, hr', hA, hNy]
    field_simp
  have hε : ρ (ι r - r) = ι r - r := by
    rw [hεdef, map_div₀, hδρ, hNyρ]
  have hν : ρ (ι r * r) = ι r * r := by
    rw [hνdef, map_div₀, h0, hNyρ]
  refine fixed_of_quadratic_roots hρ3 (ε := ι r - r) (ν := ι r * r) hε hν ?_
  ring

theorem ratio_fixed_of_three {n : ℕ} {x₁ x₂ x₃ μ₁ μ₂ μ₃ : Fin n → K}
    {c₁ c₂ c₃ t : K} (hρt : ρ t = t) (ht : t ≠ 0)
    (h₁ : x₁ = c₁ • μ₁) (h₂ : x₂ = c₂ • μ₂) (h₃ : x₃ = c₃ • μ₃)
    (hμ₁ : ∀ i, ρ (μ₁ i) = μ₁ i) (hμ₂ : ∀ i, ρ (μ₂ i) = μ₂ i) (hμ₃ : ∀ i, ρ (μ₃ i) = μ₃ i)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hc₃ : c₃ ≠ 0) (hx : x₃ = x₁ + t • x₂)
    (hind : ∀ α β : K, α • x₁ + β • x₂ = 0 → α = 0 ∧ β = 0) :
    ρ (c₁ / c₂) = c₁ / c₂ := by
  have h : c₃ • μ₃ = c₁ • μ₁ + (t * c₂) • μ₂ := by
    rw [← h₃, hx, h₁, h₂, smul_smul]
  have hρ' : ρ c₃ • μ₃ = ρ c₁ • μ₁ + (t * ρ c₂) • μ₂ := by
    funext i
    have := congrFun h i
    have := congrArg ρ this
    simpa [map_add, map_mul, hρt, hμ₁ i, hμ₂ i, hμ₃ i] using this
  have hcomb : (ρ c₃ * c₁ - c₃ * ρ c₁) • μ₁ + (t * (ρ c₃ * c₂ - c₃ * ρ c₂)) • μ₂ = 0 := by
    have e : ρ c₃ • (c₃ • μ₃) - c₃ • (ρ c₃ • μ₃) = 0 := by
      rw [smul_comm c₃ (ρ c₃) μ₃, sub_self]
    rw [h, hρ'] at e
    rw [← e]
    simp only [smul_add, smul_smul]
    module
  have hcomb' : ((ρ c₃ * c₁ - c₃ * ρ c₁) * c₁⁻¹) • x₁ +
      ((t * (ρ c₃ * c₂ - c₃ * ρ c₂)) * c₂⁻¹) • x₂ = 0 := by
    rw [h₁, h₂]
    simp only [smul_smul]
    have e1 : (ρ c₃ * c₁ - c₃ * ρ c₁) * c₁⁻¹ * c₁ = ρ c₃ * c₁ - c₃ * ρ c₁ := by
      field_simp
    have e2 : t * (ρ c₃ * c₂ - c₃ * ρ c₂) * c₂⁻¹ * c₂ = t * (ρ c₃ * c₂ - c₃ * ρ c₂) := by
      field_simp
    rw [e1, e2]
    exact hcomb
  obtain ⟨k1, k2⟩ := hind _ _ hcomb'
  have k1' : ρ c₃ * c₁ - c₃ * ρ c₁ = 0 := by
    have := mul_eq_zero.mp k1
    exact this.resolve_right (inv_ne_zero hc₁)
  have k2' : ρ c₃ * c₂ - c₃ * ρ c₂ = 0 := by
    have := (mul_eq_zero.mp k2).resolve_right (inv_ne_zero hc₂)
    exact (mul_eq_zero.mp this).resolve_left ht
  have hρc₃ : ρ c₃ ≠ 0 := (map_ne_zero ρ).mpr hc₃
  have hρc₂ : ρ c₂ ≠ 0 := (map_ne_zero ρ).mpr hc₂
  have key : ρ c₁ * c₂ = c₁ * ρ c₂ := by
    apply mul_left_cancel₀ hc₃
    linear_combination (-c₂) * k1' + c₁ * k2'
  rw [map_div₀, div_eq_div_iff hρc₂ hc₂]
  exact key

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
