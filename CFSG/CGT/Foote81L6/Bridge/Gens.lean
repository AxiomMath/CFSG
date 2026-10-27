module

public import CFSG.CGT.Foote81L6.Bridge.TModel

public section

namespace CFSG.CGT.Foote81L6.Bridge

namespace Gen

variable (n : ℕ)

@[expose] def ρ₀ : PHat n := ⟨⟨1 + hf n, 0⟩, ⟨1, 0⟩, 1, 0⟩

@[expose] def ρ₁ : PHat n := ⟨⟨-1, 0⟩, ⟨1, 0⟩, 1, 0⟩

@[expose] def κ₀ : PHat n := ⟨⟨-qr n, 1⟩, ⟨qr n, 1⟩, 1, 1⟩

@[expose] def κ₁ : PHat n := ⟨⟨qr n, 0⟩, ⟨qr n, 0⟩, 1, 1⟩

@[expose] def t : PHat n := ⟨SD.σ, 1, SD.σ, 0⟩

@[expose] def s : PHat n := ⟨⟨qr n, 0⟩, ⟨1, 1⟩, 1, 0⟩

@[expose] def rA : PHat n := ⟨1, 1, ⟨2, 0⟩, 0⟩

@[expose] def sA : PHat n := ⟨1, 1, ⟨1, 1⟩, 0⟩

@[expose] def ωt : PHat n := ⟨SD.σ, 1, SD.ω, 0⟩

@[expose] def aH : PHat n := ⟨1, 1, ⟨qr n, 0⟩, 0⟩

@[expose] def cz : PHat n := ⟨SD.z, SD.z, 1, 0⟩

variable {n}

theorem ρ₀_pow (k : ℕ) : ρ₀ n ^ k = ⟨⟨k * (1 + hf n), 0⟩, ⟨k, 0⟩, 1, 0⟩ := by
  rw [ρ₀, PHat.mk_zero_pow, SD.mk_zero_pow, SD.mk_zero_pow, one_pow, mul_one]

theorem ρ₁_pow (k : ℕ) : ρ₁ n ^ k = ⟨⟨-k, 0⟩, ⟨k, 0⟩, 1, 0⟩ := by
  rw [ρ₁, PHat.mk_zero_pow, SD.mk_zero_pow, SD.mk_zero_pow, one_pow, mul_one, mul_neg_one]

theorem ρ₁_inv_pow (k : ℕ) : (ρ₁ n)⁻¹ ^ k = ⟨⟨k, 0⟩, ⟨-k, 0⟩, 1, 0⟩ := by
  have : (ρ₁ n)⁻¹ = ⟨⟨1, 0⟩, ⟨-1, 0⟩, 1, 0⟩ := by
    ext <;> simp [ρ₁]
  rw [this, PHat.mk_zero_pow, SD.mk_zero_pow, SD.mk_zero_pow, one_pow, mul_one, mul_neg_one]

theorem rA_pow (k : ℕ) : rA n ^ k = ⟨1, 1, ⟨2 * k, 0⟩, 0⟩ := by
  rw [rA, PHat.mk_zero_pow, SD.mk_zero_pow, one_pow, mul_comm]

theorem σ_pow_even (k : ℕ) : (SD.σ : SD n) ^ (2 * k) = 1 := by
  rw [pow_mul, SD.σ_sq, one_pow]

theorem ωt_pow_even (k : ℕ) : ωt n ^ (2 * k) = ⟨1, 1, ⟨(2 * k : ℕ), 0⟩, 0⟩ := by
  rw [ωt, PHat.mk_zero_pow, σ_pow_even, one_pow, SD.ω_pow]

theorem natCast_two_pow_pred {n : ℕ} (hn : 2 ≤ n) : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) = hf n :=
  (hf_eq hn).symm

theorem natCast_two_pow_sub_two {n : ℕ} : ((2 ^ (n - 2) : ℕ) : ZMod (2 ^ n)) = qr n :=
  qr_eq.symm


syntax (name := qrClose) "qr_close " term:max term:max : tactic

macro_rules
  | `(tactic| qr_close $n $hn) => `(tactic| first
      | rfl
      | ring1
      | linear_combination four_mul_qr $n
      | linear_combination -four_mul_qr $n
      | linear_combination two_mul_qr_sq $hn
      | linear_combination -two_mul_qr_sq $hn
      | linear_combination 2 * two_mul_qr_sq $hn
      | linear_combination -2 * two_mul_qr_sq $hn
      | linear_combination -four_mul_qr $n + two_mul_qr_sq $hn
      | linear_combination four_mul_qr $n - two_mul_qr_sq $hn
      | linear_combination four_mul_qr $n - 2 * two_mul_qr_sq $hn
      | linear_combination -four_mul_qr $n + 2 * two_mul_qr_sq $hn
      | linear_combination four_mul_qr $n - 4 * two_mul_qr_sq $hn
      | linear_combination (2 - 2 * qr $n) * two_mul_qr_sq $hn
      | linear_combination (-2 + 2 * qr $n) * two_mul_qr_sq $hn
      | linear_combination 4 * two_mul_qr_sq $hn
      | linear_combination four_mul_qr $n + (-4 + 2 * qr $n) * two_mul_qr_sq $hn
      | linear_combination -four_mul_qr $n + (1 + 4 * qr $n) * two_mul_qr_sq $hn)


@[expose] def b₀H (n : ℕ) : PHat n := ⟨⟨qr n, 0⟩, ⟨qr n, 0⟩, 1, 0⟩

@[expose] def b₁H (n : ℕ) : PHat n := ⟨⟨-qr n, 0⟩, ⟨qr n, 0⟩, 1, 0⟩

section Relations

variable (hn : 3 ≤ n)
include hn

theorem κ₀_mul_ρ₀ : κ₀ n * ρ₀ n = (ρ₀ n)⁻¹ * κ₀ n := by
  ext <;> simp only [κ₀, ρ₀, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem κ₀_mul_κ₀ : κ₀ n * κ₀ n = cz n := by
  ext <;> simp only [κ₀, cz, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem κ₁_mul_ρ₁ : κ₁ n * ρ₁ n = (ρ₁ n)⁻¹ * κ₁ n := by
  ext <;> simp only [κ₁, ρ₁, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem κ₁_mul_κ₁ : κ₁ n * κ₁ n = cz n := by
  ext <;> simp only [κ₁, cz, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem ρ₀_mul_ρ₁ : ρ₀ n * ρ₁ n = ρ₁ n * ρ₀ n := by
  ext <;> simp only [ρ₀, ρ₁, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem κ₀_mul_κ₁ : κ₀ n * κ₁ n = κ₁ n * κ₀ n := by
  ext <;> simp only [κ₀, κ₁, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem ρ₀_mul_κ₁ : ρ₀ n * κ₁ n = κ₁ n * ρ₀ n * cz n := by
  ext <;> simp only [ρ₀, κ₁, cz, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem κ₀_mul_ρ₁ : κ₀ n * ρ₁ n = ρ₁ n * κ₀ n * cz n := by
  ext <;> simp only [κ₀, ρ₁, cz, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem t_mul_ρ₀ : t n * ρ₀ n = ρ₁ n * t n := by
  ext <;> simp only [t, ρ₀, ρ₁, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem t_mul_κ₀ : t n * κ₀ n = κ₁ n * t n := by
  ext <;> simp only [t, κ₀, κ₁, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem t_mul_t : t n * t n = 1 := by
  ext <;> simp only [t, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁, PHat.inv_x₂,
      PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero, PHat.sw₂_one,
      PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i, SD.inv_j,
      SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z, add_zero,
      zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem s_mul_ρ₀ : s n * ρ₀ n = ρ₁ n ^ (θ n).val * s n := by
  rw [ρ₁_pow, ZMod.natCast_zmod_val]
  ext <;> simp only [s, ρ₀, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem s_mul_κ₀ : s n * κ₀ n = κ₁ n * (ρ₁ n)⁻¹ ^ (1 + (qr n).val) * s n := by
  rw [ρ₁_inv_pow, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  ext <;> simp only [s, κ₀, κ₁, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem s_mul_s : s n * s n = cz n := by
  ext <;> simp only [s, cz, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem s_mul_ρ₁ : s n * ρ₁ n = ρ₀ n ^ (θ n).val * s n := by
  rw [ρ₀_pow, ZMod.natCast_zmod_val]
  ext <;> simp only [s, ρ₁, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem s_mul_κ₁ : s n * κ₁ n = κ₀ n * ρ₀ n ^ (2 ^ (n - 2) - 1) * s n := by
  rw [ρ₀_pow, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one, natCast_two_pow_sub_two]
  ext <;> simp only [s, κ₀, κ₁, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem t_mul_s : t n * s n = s n * b₀H n * b₁H n * cz n * t n := by
  ext <;> simp only [t, s, b₀H, b₁H, cz, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e,
      PHat.inv_x₁, PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem ρ₀_pow_qr : ρ₀ n ^ 2 ^ (n - 2) = b₀H n := by
  rw [ρ₀_pow, natCast_two_pow_sub_two]
  ext <;> simp only [b₀H, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem ρ₁_pow_qr : ρ₁ n ^ 2 ^ (n - 2) = b₁H n := by
  rw [ρ₁_pow, natCast_two_pow_sub_two]
  rfl

theorem ρ₀_pow_hf : ρ₀ n ^ 2 ^ (n - 1) = cz n := by
  rw [ρ₀_pow, natCast_two_pow_pred (by omega)]
  ext <;> simp only [cz, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem ρ₁_pow_hf : ρ₁ n ^ 2 ^ (n - 1) = cz n := by
  rw [ρ₁_pow, natCast_two_pow_pred (by omega)]
  ext <;> simp only [cz, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem sA_mul_rA : sA n * rA n = (rA n)⁻¹ * sA n := by
  ext <;> simp only [sA, rA, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem sA_mul_sA : sA n * sA n = PHat.zF := by
  ext <;> simp only [sA, PHat.zF, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem rA_pow_qr : rA n ^ 2 ^ (n - 2) = PHat.zF := by
  rw [rA_pow, natCast_two_pow_sub_two]
  ext <;> simp only [PHat.zF, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem rA_pow_qr_half : rA n ^ 2 ^ (n - 3) = aH n := by
  have h2 : 2 * ((2 ^ (n - 3) : ℕ) : ZMod (2 ^ n)) = qr n := by
    rw [qr]
    push_cast
    rw [← pow_succ']
    congr 1
    omega
  rw [rA_pow, h2]
  rfl

theorem t_mul_ωt : t n * ωt n = (ωt n)⁻¹ * PHat.zF * t n := by
  ext <;> simp only [t, ωt, PHat.zF, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem ωt_mul_ωt : ωt n * ωt n = rA n := by
  ext <;> simp only [ωt, rA, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem sA_mul_zF : sA n * PHat.zF = ωt n * ωt n * t n * ωt n := by
  ext <;> simp only [sA, PHat.zF, ωt, t, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e,
      PHat.inv_x₁, PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem t_mul_rA : t n * rA n = (rA n)⁻¹ * t n := by
  ext <;> simp only [t, rA, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem t_mul_sA : t n * sA n = rA n ^ (2 ^ (n - 2) - 1) * sA n * t n := by
  rw [rA_pow, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one, natCast_two_pow_sub_two]
  ext <;> simp only [t, sA, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃, PHat.mul_e, PHat.inv_x₁,
      PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one, PHat.sw₂_zero,
      PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i, SD.mul_j, SD.inv_i,
      SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr, SD.σ, SD.ω, SD.z,
      add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem ωt_pow_hf : ωt n ^ 2 ^ (n - 1) = PHat.zF := by
  rw [show 2 ^ (n - 1) = 2 * 2 ^ (n - 2) by rw [← pow_succ']; congr 1; omega, ωt_pow_even,
    ← show 2 ^ (n - 1) = 2 * 2 ^ (n - 2) by rw [← pow_succ']; congr 1; omega,
    natCast_two_pow_pred (by omega)]
  rfl

theorem ωt_pow_qr : ωt n ^ 2 ^ (n - 2) = aH n := by
  rw [show 2 ^ (n - 2) = 2 * 2 ^ (n - 3) by rw [← pow_succ']; congr 1; omega, ωt_pow_even,
    ← show 2 ^ (n - 2) = 2 * 2 ^ (n - 3) by rw [← pow_succ']; congr 1; omega,
    natCast_two_pow_sub_two]
  rfl

end Relations

theorem cz_eq : cz n = PHat.c * PHat.zF := by
  ext <;> simp [cz, PHat.c, PHat.zF, SD.z_mul_self]

theorem cz_comm (a : PHat n) : a * cz n = cz n * a := by
  rw [cz_eq, ← mul_assoc, PHat.c_comm, mul_assoc, PHat.zF_comm, mul_assoc]

end Gen

end CFSG.CGT.Foote81L6.Bridge
