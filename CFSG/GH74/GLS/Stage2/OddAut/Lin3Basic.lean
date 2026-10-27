module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix

section Scalar

variable {K : Type*} [Field K]

theorem coe_scalar_smul (u : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (u : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem scalar_commute (u : Kˣ) (g : GL (Fin 3) K) :
    Commute (GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) g := by
  apply Units.ext
  show (GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K).1 * g.1 = g.1 * (GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K).1
  rw [coe_scalar_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem scalar_injective : Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K) := by
  intro u v h
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp only [coe_scalar_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
  exact Units.ext h1

theorem det_scalar (u : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) = u ^ 3 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_scalar_smul, Matrix.det_smul, Matrix.det_one]
  simp

theorem comm_scalar_cube {a b : GL (Fin 3) K} {u : Kˣ}
    (h : a * b = GeneralLinearGroup.scalar (Fin 3) u * (b * a)) : u ^ 3 = 1 := by
  have h1 := congrArg (GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ) h
  rw [map_mul, map_mul, map_mul, det_scalar] at h1
  have h2 : u ^ 3 * (GeneralLinearGroup.det b * GeneralLinearGroup.det a) =
      1 * (GeneralLinearGroup.det b * GeneralLinearGroup.det a) :=
    calc u ^ 3 * (GeneralLinearGroup.det b * GeneralLinearGroup.det a)
        = GeneralLinearGroup.det a * GeneralLinearGroup.det b := h1.symm
      _ = 1 * (GeneralLinearGroup.det b * GeneralLinearGroup.det a) := by rw [one_mul, mul_comm]
  exact mul_right_cancel h2

theorem comm_scalar_pow {a b : GL (Fin 3) K} {u : Kˣ} {r : ℕ} {β : Kˣ}
    (h : a * b = GeneralLinearGroup.scalar (Fin 3) u * (b * a))
    (hb : b ^ r = GeneralLinearGroup.scalar (Fin 3) β) : u ^ r = 1 := by
  have hconj : a * b * a⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * b := by
    calc a * b * a⁻¹ = (GeneralLinearGroup.scalar (Fin 3) u * (b * a)) * a⁻¹ := by rw [h]
      _ = GeneralLinearGroup.scalar (Fin 3) u * b := by group
  have h1 : a * b ^ r * a⁻¹ = (a * b * a⁻¹) ^ r := by
    simp
  rw [hconj, (scalar_commute u b).mul_pow r, hb] at h1
  have h3 : a * GeneralLinearGroup.scalar (Fin 3) β * a⁻¹ = GeneralLinearGroup.scalar (Fin 3) β := by
    rw [← (scalar_commute β a).eq, mul_inv_cancel_right]
  rw [h3, ← map_pow, ← map_mul] at h1
  have := scalar_injective h1
  have h5 : u ^ r * β = 1 * β := by rw [one_mul]; exact this.symm
  exact mul_right_cancel h5

theorem heis_r_eq_three {a b : GL (Fin 3) K} {u : Kˣ} {r : ℕ} {β : Kˣ} (hr : r.Prime)
    (h : a * b = GeneralLinearGroup.scalar (Fin 3) u * (b * a))
    (hb : b ^ r = GeneralLinearGroup.scalar (Fin 3) β) (hu : u ≠ 1) : r = 3 := by
  have h3 := comm_scalar_cube h
  have hr' := comm_scalar_pow h hb
  have : Fact r.Prime := ⟨hr⟩
  have e1 : orderOf u = r := orderOf_eq_prime hr' hu
  have e2 : orderOf u = 3 := orderOf_eq_prime (p := 3) h3 hu
  rw [← e1, e2]

end Scalar

section Exponents

theorem dvd_aux (r q1 q2 ρ τ σ : ℕ) (h : ρ + σ = r) :
    r ∣ (r * q1 + ρ) * τ + (r * q2 + τ) * σ :=
  ⟨q1 * τ + q2 * σ + τ, by subst h; ring⟩

variable {K : Type*} [Field K] [Finite K]

theorem exists_exponents_pow {r : ℕ} (hr : r.Prime) (α β : Kˣ) :
    ∃ (i j : ℕ) (γ : Kˣ), i < r ∧ j < r ∧ (i ≠ 0 ∨ j ≠ 0) ∧ α ^ i * β ^ j = γ ^ r := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hpow : ∀ x : Kˣ, ∃ n : ℕ, g ^ n = x := by
    intro x
    exact (Submonoid.mem_powers_iff x g).mp (mem_powers_iff_mem_zpowers.mpr (hg x))
  obtain ⟨s, hs⟩ := hpow α
  obtain ⟨t, ht⟩ := hpow β
  have hr0 : 0 < r := hr.pos
  by_cases hrs : r ∣ s
  · obtain ⟨q, hq⟩ := hrs
    refine ⟨1, 0, g ^ q, hr.one_lt, hr0, Or.inl one_ne_zero, ?_⟩
    rw [← hs, pow_one, pow_zero, mul_one, hq, ← pow_mul, mul_comm]
  · have hρ : s % r ≠ 0 := fun h => hrs (Nat.dvd_of_mod_eq_zero h)
    have hρlt : s % r < r := Nat.mod_lt _ hr0
    have hτlt : t % r < r := Nat.mod_lt _ hr0
    have hdiv : r ∣ s * (t % r) + t * (r - s % r) := by
      have h := dvd_aux r (s / r) (t / r) (s % r) (t % r) (r - s % r) (by omega)
      rwa [Nat.div_add_mod, Nat.div_add_mod] at h
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨t % r, r - s % r, g ^ q, hτlt, by omega, Or.inr (by omega), ?_⟩
    rw [← hs, ← ht, ← pow_mul, ← pow_mul, ← pow_add, hq, ← pow_mul, mul_comm]

end Exponents

end CFSG.GH74.GLS.Stage2.OddAut
