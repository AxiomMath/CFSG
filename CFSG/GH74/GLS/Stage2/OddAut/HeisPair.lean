module

public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Basic

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

section Comm

variable {G : Type*} [Group G]

theorem mul_pow_comm_central {a b c : G} (hc : ∀ g : G, Commute g c) (hab : a * b = c * (b * a))
    (j : ℕ) : a * b ^ j = c ^ j * (b ^ j * a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc a * b ^ (j + 1) = (a * b ^ j) * b := by rw [pow_succ, ← mul_assoc]
      _ = (c ^ j * (b ^ j * a)) * b := by rw [ih]
      _ = c ^ j * (b ^ j * (a * b)) := by simp only [mul_assoc]
      _ = c ^ j * (b ^ j * (c * (b * a))) := by rw [hab]
      _ = c ^ j * ((b ^ j * c) * (b * a)) := by simp only [mul_assoc]
      _ = c ^ j * ((c * b ^ j) * (b * a)) := by rw [(hc (b ^ j)).eq]
      _ = (c ^ j * c) * (b ^ j * (b * a)) := by simp only [mul_assoc]
      _ = c ^ (j + 1) * (b ^ (j + 1) * a) := by rw [← pow_succ, ← mul_assoc (b ^ j), ← pow_succ]

theorem pow_mul_pow_comm_central {a b c : G} (hc : ∀ g : G, Commute g c) (hab : a * b = c * (b * a))
    (i j : ℕ) : a ^ i * b ^ j = c ^ (i * j) * (b ^ j * a ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc a ^ (i + 1) * b ^ j = a * (a ^ i * b ^ j) := by rw [pow_succ', mul_assoc]
      _ = a * (c ^ (i * j) * (b ^ j * a ^ i)) := by rw [ih]
      _ = (a * c ^ (i * j)) * (b ^ j * a ^ i) := by simp only [mul_assoc]
      _ = (c ^ (i * j) * a) * (b ^ j * a ^ i) := by rw [((hc a).pow_right (i * j)).eq]
      _ = c ^ (i * j) * ((a * b ^ j) * a ^ i) := by simp only [mul_assoc]
      _ = c ^ (i * j) * ((c ^ j * (b ^ j * a)) * a ^ i) := by rw [mul_pow_comm_central hc hab j]
      _ = (c ^ (i * j) * c ^ j) * (b ^ j * (a * a ^ i)) := by simp only [mul_assoc]
      _ = c ^ ((i + 1) * j) * (b ^ j * a ^ (i + 1)) := by
          rw [← pow_add, ← pow_succ', add_mul, one_mul]

theorem cube_mul_central {x y c : G} (hc : ∀ g : G, Commute g c) (hxy : x * y = c * (y * x))
    (hc3 : c ^ 3 = 1) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  set t : G := c⁻¹ with ht
  have htc : ∀ g : G, g * t = t * g := fun g => ((hc g).inv_right).eq
  have hyx : y * x = t * (x * y) := by
    rw [hxy, ht]; group
  have ht3 : t ^ 3 = 1 := by rw [ht, inv_pow, hc3, inv_one]
  have hmv : ∀ g h : G, g * (t * h) = t * (g * h) := fun g h => by
    rw [← mul_assoc, htc g, mul_assoc]
  have h2 : (x * y) * (x * y) = t * (x ^ 2 * y ^ 2) := by
    calc (x * y) * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (t * (x * y)) * y := by rw [hyx]
      _ = t * (x * (x * y)) * y := by rw [hmv]
      _ = t * (x ^ 2 * y ^ 2) := by simp only [mul_assoc, pow_two]
  have h3 : y ^ 2 * x = t * t * (x * y ^ 2) := by
    calc y ^ 2 * x = y * (y * x) := by simp only [mul_assoc, pow_two]
      _ = y * (t * (x * y)) := by rw [hyx]
      _ = t * (y * (x * y)) := by rw [hmv]
      _ = t * ((y * x) * y) := by simp only [mul_assoc]
      _ = t * ((t * (x * y)) * y) := by rw [hyx]
      _ = t * (t * (x * y * y)) := by simp only [mul_assoc]
      _ = t * t * (x * y ^ 2) := by simp only [mul_assoc, pow_two]
  have h4 : x ^ 2 * (t * t * (x * y ^ 2)) = t * t * (x ^ 2 * (x * y ^ 2)) := by
    rw [mul_assoc t t, hmv, hmv, ← mul_assoc t t]
  calc (x * y) ^ 3 = (x * y) * (x * y) * (x * y) := by simp only [pow_succ, pow_zero, one_mul]
    _ = (t * (x ^ 2 * y ^ 2)) * (x * y) := by rw [h2]
    _ = t * (x ^ 2 * (y ^ 2 * x) * y) := by simp only [mul_assoc]
    _ = t * (x ^ 2 * (t * t * (x * y ^ 2)) * y) := by rw [h3]
    _ = t * (t * t * (x ^ 2 * (x * y ^ 2)) * y) := by rw [h4]
    _ = t * (t * t * (x ^ 2 * (x * y ^ 2) * y)) := by simp only [mul_assoc]
    _ = t ^ 3 * (x ^ 3 * y ^ 3) := by
        simp only [mul_assoc, pow_succ, pow_zero, one_mul]
    _ = x ^ 3 * y ^ 3 := by rw [ht3, one_mul]

end Comm

open Matrix

section Pair

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem ne_one_of_pow_three {u : Kˣ} (hu : u ≠ 1) (hu3 : u ^ 3 = 1) {j : ℕ} (hj : j < 3) (hj0 : j ≠ 0) :
    u ^ j ≠ 1 := by
  intro h
  interval_cases j
  · exact hj0 rfl
  · exact hu (by simpa using h)
  · apply hu
    calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
      _ = 1 := by rw [hu3, h]; simp

theorem exists_cube_pair (a b : GL (Fin 3) K) (ua ub u : Kˣ)
    (ha : a ^ 3 = GeneralLinearGroup.scalar (Fin 3) ua) (hb : b ^ 3 = GeneralLinearGroup.scalar (Fin 3) ub)
    (hab : a * b = GeneralLinearGroup.scalar (Fin 3) u * (b * a)) (hu : u ≠ 1) :
    ∃ (i j : ℕ) (γ : Kˣ) (y : GL (Fin 3) K) (ξ : Kˣ),
      (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j)) ^ 3 = 1 ∧
      (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j)) * y =
        GeneralLinearGroup.scalar (Fin 3) ξ * (y * (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j))) ∧
      ξ ≠ 1 ∧ (i ≠ 0 ∨ j ≠ 0) := by
  have hu3 := comm_scalar_cube hab
  have hcent : ∀ (w : Kˣ) (g : GL (Fin 3) K), Commute g (GeneralLinearGroup.scalar (Fin 3) w) :=
    fun w g => (scalar_commute w g).symm
  obtain ⟨i, j, γ, hi, hj, hij, hγ⟩ := exists_exponents_pow Nat.prime_three ua ub
  have hcube : (a ^ i * b ^ j) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (γ ^ 3) := by
    have hc : ∀ g : GL (Fin 3) K, Commute g (GeneralLinearGroup.scalar (Fin 3) u ^ (i * j)) :=
      fun g => (hcent u g).pow_right _
    have hxy := pow_mul_pow_comm_central (fun g => hcent u g) hab i j
    have hc3 : (GeneralLinearGroup.scalar (Fin 3) u ^ (i * j)) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hu3, map_one, one_pow]
    rw [cube_mul_central hc hxy hc3, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3, pow_mul,
      pow_mul, ha, hb, ← map_pow, ← map_pow, ← map_mul, ← hγ]
  have hcubex : (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j)) ^ 3 = 1 := by
    rw [(scalar_commute γ⁻¹ _).mul_pow, hcube, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hmv : ∀ (w : Kˣ) (g h : GL (Fin 3) K),
      g * (GeneralLinearGroup.scalar (Fin 3) w * h) = GeneralLinearGroup.scalar (Fin 3) w * (g * h) :=
    fun w g h => by rw [← mul_assoc, (scalar_commute w g).symm.eq, mul_assoc]
  by_cases hj0 : j = 0
  · have hi0 : i ≠ 0 := by rcases hij with h | h; exact h; exact absurd hj0 h
    subst hj0
    have h1 : a ^ i * b = GeneralLinearGroup.scalar (Fin 3) u ^ i * (b * a ^ i) := by
      have := pow_mul_pow_comm_central (fun g => hcent u g) hab i 1
      simpa using this
    refine ⟨i, 0, γ, b, u ^ i, hcubex, ?_, ne_one_of_pow_three hu hu3 hi hi0, Or.inl hi0⟩
    rw [pow_zero, mul_one]
    have e : GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * GeneralLinearGroup.scalar (Fin 3) u ^ i =
        GeneralLinearGroup.scalar (Fin 3) (u ^ i) * GeneralLinearGroup.scalar (Fin 3) γ⁻¹ := by
      rw [← map_pow, ← map_mul, ← map_mul, mul_comm]
    calc GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * a ^ i * b
        = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b) := mul_assoc _ _ _
      _ = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ *
            (GeneralLinearGroup.scalar (Fin 3) u ^ i * (b * a ^ i)) := by rw [h1]
      _ = (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * GeneralLinearGroup.scalar (Fin 3) u ^ i) *
            (b * a ^ i) := by rw [mul_assoc]
      _ = (GeneralLinearGroup.scalar (Fin 3) (u ^ i) * GeneralLinearGroup.scalar (Fin 3) γ⁻¹) *
            (b * a ^ i) := by rw [e]
      _ = GeneralLinearGroup.scalar (Fin 3) (u ^ i) *
            (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (b * a ^ i)) := by rw [mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin 3) (u ^ i) *
            (b * (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * a ^ i)) := by
          rw [← hmv γ⁻¹ b (a ^ i)]
  · have hj3 : j ≠ 0 := hj0
    have hbj : b ^ j * a = GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) * (a * b ^ j) := by
      have := mul_pow_comm_central (fun g => hcent u g) hab j
      rw [this, map_inv, map_pow, inv_mul_cancel_left]
    refine ⟨i, j, γ, a, (u ^ j)⁻¹, hcubex, ?_, ?_, Or.inr hj3⟩
    · have hai : ∀ w : GL (Fin 3) K, a ^ i * (a * w) = a * (a ^ i * w) := fun w => by
        rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_succ']
      have e : GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) =
          GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) * GeneralLinearGroup.scalar (Fin 3) γ⁻¹ := by
        rw [← map_mul, ← map_mul, mul_comm]
      calc GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j) * a
          = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * (b ^ j * a)) := by
            simp only [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i *
              (GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) * (a * b ^ j))) := by rw [hbj]
        _ = GeneralLinearGroup.scalar (Fin 3) γ⁻¹ *
              (GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) * (a ^ i * (a * b ^ j))) := by
            rw [hmv]
        _ = (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹)) *
              (a ^ i * (a * b ^ j)) := by rw [mul_assoc]
        _ = (GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) * GeneralLinearGroup.scalar (Fin 3) γ⁻¹) *
              (a ^ i * (a * b ^ j)) := by rw [e]
        _ = GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) *
              (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * (a * b ^ j))) := by rw [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) *
              (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a * (a ^ i * b ^ j))) := by rw [hai]
        _ = GeneralLinearGroup.scalar (Fin 3) ((u ^ j)⁻¹) *
              (a * (GeneralLinearGroup.scalar (Fin 3) γ⁻¹ * (a ^ i * b ^ j))) := by
            rw [← hmv γ⁻¹ a (a ^ i * b ^ j)]
    · exact inv_ne_one.mpr (ne_one_of_pow_three hu hu3 hj hj3)

end Pair

end CFSG.GH74.GLS.Stage2.OddAut
