module

public import CFSG.ClassicalInvolution.Asc77.AscC5O5M8

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

variable {F : Type} [Field F] [Finite F]

theorem twist_ratio_swap {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2) {ν ρ θ : F}
    (hν : ν ≠ 0) (π τ : F ≃+* F) (hρ : ρ ^ 2 = ν * π ν) (hθ : θ ^ 2 * ν = τ ν) :
    τ ρ = ρ * π θ * θ := by
  obtain ⟨i, hi⟩ := C5O.exists_eq_pow_of_ringEquiv (p := p) π
  obtain ⟨j, hj⟩ := C5O.exists_eq_pow_of_ringEquiv (p := p) τ
  have hpo : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨a, ha⟩ := hpo.pow (n := i)
  obtain ⟨b, hb⟩ := hpo.pow (n := j)
  have hρ' : ρ ^ 2 = (ν ^ (a + 1)) ^ 2 := by
    rw [hρ, hi, ha]
    ring
  have hθ' : θ ^ 2 = (ν ^ b) ^ 2 := by
    refine mul_right_cancel₀ hν ?_
    rw [hθ, hj, hb]
    ring
  have hodd : ∀ x : F, (-x) ^ (2 * a + 1) = -x ^ (2 * a + 1) := fun x => by
    rw [Odd.neg_pow ⟨a, rfl⟩]
  have hodd' : ∀ x : F, (-x) ^ (2 * b + 1) = -x ^ (2 * b + 1) := fun x => by
    rw [Odd.neg_pow ⟨b, rfl⟩]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hρ' with h1 | h1 <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hθ' with h2 | h2 <;>
    rw [h1, h2, hi, hj, ha, hb] <;> (try simp only [hodd, hodd']) <;> ring

theorem fix_ratio {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2) (σ τ : F ≃+* F)
    {ν₀ ν₁ μ μ' η η' : F} (hν₀ : ν₀ ≠ 0) (hν₁ : ν₁ ≠ 0) (hμ : μ ≠ 0) (hη : η ≠ 0)
    (ℓ₀ ℓ₁ κ₀ κ₁ : Fˣ)
    (hℓ₀ : μ' * σ ν₀ = (ℓ₀ : F) ^ 2 * ν₀ * μ) (hℓ₁ : μ' * σ ν₁ = (ℓ₁ : F) ^ 2 * ν₁ * μ)
    (hκ₀ : η' * τ ν₀ = (κ₀ : F) ^ 2 * ν₀ * η) (hκ₁ : η' * τ ν₁ = (κ₁ : F) ^ 2 * ν₁ * η) :
    ℓ₀ * Units.map (σ : F →* F) κ₀ * (Units.map (τ : F →* F) ℓ₀)⁻¹ * κ₀⁻¹ =
      ℓ₁ * Units.map (σ : F →* F) κ₁ * (Units.map (τ : F →* F) ℓ₁)⁻¹ * κ₁⁻¹ := by
  have hσ₁ : σ ν₁ ≠ 0 := (map_ne_zero σ).mpr hν₁
  have hτ₁ : τ ν₁ ≠ 0 := (map_ne_zero τ).mpr hν₁
  have hl' : (ℓ₁ : F) ^ 2 * σ ν₀ * ν₁ = (ℓ₀ : F) ^ 2 * ν₀ * σ ν₁ :=
    mul_right_cancel₀ hμ (by linear_combination σ ν₁ * hℓ₀ - σ ν₀ * hℓ₁)
  have hk' : (κ₁ : F) ^ 2 * τ ν₀ * ν₁ = (κ₀ : F) ^ 2 * ν₀ * τ ν₁ :=
    mul_right_cancel₀ hη (by linear_combination τ ν₁ * hκ₀ - τ ν₀ * hκ₁)
  have hl : (ℓ₁ : F) ^ 2 * σ (ν₀ / ν₁) = (ℓ₀ : F) ^ 2 * (ν₀ / ν₁) := by
    rw [map_div₀, mul_div_assoc', mul_div_assoc', div_eq_div_iff hσ₁ hν₁]
    linear_combination hl'
  have hk : (κ₁ : F) ^ 2 * τ (ν₀ / ν₁) = (κ₀ : F) ^ 2 * (ν₀ / ν₁) := by
    rw [map_div₀, mul_div_assoc', mul_div_assoc', div_eq_div_iff hτ₁ hν₁]
    linear_combination hk'
  have h := C5O.block_ratio_eq hp (div_ne_zero hν₀ hν₁) ℓ₀.ne_zero κ₀.ne_zero σ τ hl hk
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass]
  have h1 : τ (ℓ₀ : F) ≠ 0 := (map_ne_zero τ).mpr ℓ₀.ne_zero
  have h2 : τ (ℓ₁ : F) ≠ 0 := (map_ne_zero τ).mpr ℓ₁.ne_zero
  rw [show (ℓ₀ : F) * σ κ₀ * (τ ℓ₀)⁻¹ * (κ₀ : F)⁻¹ = ℓ₀ * σ κ₀ / (τ ℓ₀ * κ₀) by ring,
    show (ℓ₁ : F) * σ κ₁ * (τ ℓ₁)⁻¹ * (κ₁ : F)⁻¹ = ℓ₁ * σ κ₁ / (τ ℓ₁ * κ₁) by ring,
    div_eq_div_iff (mul_ne_zero h1 κ₀.ne_zero) (mul_ne_zero h2 κ₁.ne_zero)]
  linear_combination h

theorem swap_ratio {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2) (π τ : F ≃+* F)
    {ν₀ ν₁ μ μ' η η' : F} (hν₀ : ν₀ ≠ 0) (hν₁ : ν₁ ≠ 0) (hμ : μ ≠ 0) (hη : η ≠ 0)
    (lam₀ lam₁ κ₀ κ₁ : Fˣ)
    (hl₀ : μ' * π ν₀ * ν₀ = (lam₀ : F) ^ 2 * μ) (hl₁ : μ' * π ν₁ * ν₁ = (lam₁ : F) ^ 2 * μ)
    (hκ₀ : η' * τ ν₀ = (κ₀ : F) ^ 2 * ν₀ * η) (hκ₁ : η' * τ ν₁ = (κ₁ : F) ^ 2 * ν₁ * η) :
    lam₀ * Units.map (π : F →* F) κ₀ * (Units.map (τ : F →* F) lam₀)⁻¹ * κ₀ =
      lam₁ * Units.map (π : F →* F) κ₁ * (Units.map (τ : F →* F) lam₁)⁻¹ * κ₁ := by
  have hπ₀ : π ν₀ ≠ 0 := (map_ne_zero π).mpr hν₀
  have hτ₀ : τ ν₀ ≠ 0 := (map_ne_zero τ).mpr hν₀
  have hl0 : (lam₀ : F) ≠ 0 := lam₀.ne_zero
  have hk0 : (κ₀ : F) ≠ 0 := κ₀.ne_zero
  have hl' : (lam₁ : F) ^ 2 * (ν₀ * π ν₀) = (lam₀ : F) ^ 2 * (ν₁ * π ν₁) :=
    mul_right_cancel₀ hμ (by linear_combination ν₁ * π ν₁ * hl₀ - ν₀ * π ν₀ * hl₁)
  have hk' : (κ₁ : F) ^ 2 * ν₁ * τ ν₀ = (κ₀ : F) ^ 2 * ν₀ * τ ν₁ :=
    mul_right_cancel₀ hη (by linear_combination τ ν₁ * hκ₀ - τ ν₀ * hκ₁)
  have hρ : ((lam₁ : F) / lam₀) ^ 2 = ν₁ / ν₀ * π (ν₁ / ν₀) := by
    rw [map_div₀, div_pow, div_mul_div_comm, div_eq_div_iff (pow_ne_zero 2 hl0)
      (mul_ne_zero hν₀ hπ₀)]
    linear_combination hl'
  have hθ : ((κ₁ : F) / κ₀) ^ 2 * (ν₁ / ν₀) = τ (ν₁ / ν₀) := by
    rw [map_div₀, div_pow, div_mul_div_comm, div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hk0) hν₀)
      hτ₀]
    linear_combination hk'
  have h := twist_ratio_swap hp (div_ne_zero hν₁ hν₀) π τ hρ hθ
  rw [map_div₀, map_div₀] at h
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass]
  have h1 : τ (lam₀ : F) ≠ 0 := (map_ne_zero τ).mpr hl0
  have h2 : τ (lam₁ : F) ≠ 0 := (map_ne_zero τ).mpr lam₁.ne_zero
  have h3 : π (κ₀ : F) ≠ 0 := (map_ne_zero π).mpr hk0
  rw [div_eq_iff h1, div_mul_div_comm, div_mul_div_comm, div_mul_eq_mul_div, eq_div_iff
    (mul_ne_zero (mul_ne_zero hl0 h3) hk0)] at h
  rw [show (lam₀ : F) * π κ₀ * (τ lam₀)⁻¹ * κ₀ = lam₀ * π κ₀ * κ₀ / τ lam₀ by ring,
    show (lam₁ : F) * π κ₁ * (τ lam₁)⁻¹ * κ₁ = lam₁ * π κ₁ * κ₁ / τ lam₁ by ring,
    div_eq_div_iff h1 h2]
  linear_combination h

end CFSG.ClassicalInvolution.Asc77.C5O.M
