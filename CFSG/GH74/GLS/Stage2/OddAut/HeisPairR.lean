module

public import CFSG.GH74.GLS.Stage2.OddAut.HeisPair
public import CFSG.GH74.GLS.Stage2.OddAut.LinNAut

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix

section CommR

variable {G : Type*} [Group G]

theorem pow_mul_central {x y t : G} (ht : ∀ g : G, Commute g t) (hyx : y * x = t * (x * y))
    (m : ℕ) : (x * y) ^ m = t ^ (m.choose 2) * (x ^ m * y ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hyxm : y ^ m * x = t ^ m * (x * y ^ m) := by simpa using pow_mul_pow_comm_central ht hyx m 1
    calc (x * y) ^ (m + 1) = (x * y) ^ m * (x * y) := pow_succ _ _
      _ = (t ^ (m.choose 2) * (x ^ m * y ^ m)) * (x * y) := by rw [ih]
      _ = t ^ (m.choose 2) * (x ^ m * (y ^ m * x) * y) := by simp only [mul_assoc]
      _ = t ^ (m.choose 2) * (x ^ m * (t ^ m * (x * y ^ m)) * y) := by rw [hyxm]
      _ = t ^ (m.choose 2) * (t ^ m * (x ^ m * (x * y ^ m) * y)) := by
          have : x ^ m * (t ^ m * (x * y ^ m)) = t ^ m * (x ^ m * (x * y ^ m)) := by
            rw [← mul_assoc, ((ht (x ^ m)).pow_right m).eq, mul_assoc]
          rw [this]
          simp only [mul_assoc]
      _ = (t ^ (m.choose 2) * t ^ m) * (x ^ (m + 1) * y ^ (m + 1)) := by
          simp only [mul_assoc, pow_succ]
      _ = t ^ ((m + 1).choose 2) * (x ^ (m + 1) * y ^ (m + 1)) := by
          have : (m + 1).choose 2 = m.choose 2 + m := by
            rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
          rw [← pow_add, this]

theorem pow_odd_mul_central {x y c : G} (hc : ∀ g : G, Commute g c) (hxy : x * y = c * (y * x))
    {r : ℕ} (hr : Odd r) (hcr : c ^ r = 1) : (x * y) ^ r = x ^ r * y ^ r := by
  have ht : ∀ g : G, Commute g c⁻¹ := fun g => (hc g).inv_right
  have hyx : y * x = c⁻¹ * (x * y) := by
    rw [hxy]; group
  have h1 := pow_mul_central ht hyx r
  obtain ⟨k, hk⟩ := hr
  have h2 : r.choose 2 = r * k := by
    rw [Nat.choose_two_right, hk]
    have : (2 * k + 1) * (2 * k + 1 - 1) = 2 * ((2 * k + 1) * k) := by
      rw [Nat.add_sub_cancel]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have h3 : (c⁻¹) ^ (r.choose 2) = 1 := by
    rw [h2, pow_mul, inv_pow, hcr, inv_one, one_pow]
  rw [h1, h3, one_mul]

end CommR

section PairR

variable {K : Type} [Field K] {n : ℕ}

omit [Field K] in
theorem pow_ne_one_of_lt_prime {M : Type*} [Monoid M] {u : M} {r : ℕ} (hr : r.Prime) (hu : u ≠ 1)
    (hur : u ^ r = 1) {j : ℕ} (hj : j < r) (hj0 : j ≠ 0) : u ^ j ≠ 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have h1 : orderOf u = r := orderOf_eq_prime hur hu
  exact pow_ne_one_of_lt_orderOf hj0 (by rw [h1]; exact hj)

theorem exists_pow_pair [Finite K] {r : ℕ} (hr : r.Prime) (hr2 : Odd r) (a b : GL (Fin n) K)
    (ua ub u : Kˣ)
    (ha : a ^ r = GeneralLinearGroup.scalar (Fin n) ua)
    (hb : b ^ r = GeneralLinearGroup.scalar (Fin n) ub)
    (hab : a * b = GeneralLinearGroup.scalar (Fin n) u * (b * a)) (hu : u ≠ 1) (hur : u ^ r = 1) :
    ∃ (i j : ℕ) (γ : Kˣ) (y : GL (Fin n) K) (ξ : Kˣ),
      (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j)) ^ r = 1 ∧
      (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j)) * y =
        GeneralLinearGroup.scalar (Fin n) ξ *
          (y * (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j))) ∧
      ξ ≠ 1 ∧ (i ≠ 0 ∨ j ≠ 0) := by
  have hcent : ∀ (w : Kˣ) (g : GL (Fin n) K), Commute g (GeneralLinearGroup.scalar (Fin n) w) :=
    fun w g => (scalar_commute_n w g).symm
  obtain ⟨i, j, γ, hi, hj, hij, hγ⟩ := exists_exponents_pow hr ua ub
  have hcube : (a ^ i * b ^ j) ^ r = GeneralLinearGroup.scalar (Fin n) (γ ^ r) := by
    have hc : ∀ g : GL (Fin n) K, Commute g (GeneralLinearGroup.scalar (Fin n) u ^ (i * j)) :=
      fun g => (hcent u g).pow_right _
    have hxy := pow_mul_pow_comm_central (fun g => hcent u g) hab i j
    have hc3 : (GeneralLinearGroup.scalar (Fin n) u ^ (i * j)) ^ r = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hur, map_one, one_pow]
    rw [pow_odd_mul_central hc hxy hr2 hc3, ← pow_mul, ← pow_mul, mul_comm i r, mul_comm j r, pow_mul,
      pow_mul, ha, hb, ← map_pow, ← map_pow, ← map_mul, ← hγ]
  have hcubex : (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j)) ^ r = 1 := by
    rw [(scalar_commute_n γ⁻¹ _).mul_pow, hcube, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hmv : ∀ (w : Kˣ) (g h : GL (Fin n) K),
      g * (GeneralLinearGroup.scalar (Fin n) w * h) = GeneralLinearGroup.scalar (Fin n) w * (g * h) :=
    fun w g h => by rw [← mul_assoc, (scalar_commute_n w g).symm.eq, mul_assoc]
  by_cases hj0 : j = 0
  · have hi0 : i ≠ 0 := by rcases hij with h | h; exact h; exact absurd hj0 h
    subst hj0
    have h1 : a ^ i * b = GeneralLinearGroup.scalar (Fin n) u ^ i * (b * a ^ i) := by
      have := pow_mul_pow_comm_central (fun g => hcent u g) hab i 1
      simpa using this
    refine ⟨i, 0, γ, b, u ^ i, hcubex, ?_, pow_ne_one_of_lt_prime hr hu hur hi hi0, Or.inl hi0⟩
    rw [pow_zero, mul_one]
    have e : GeneralLinearGroup.scalar (Fin n) γ⁻¹ * GeneralLinearGroup.scalar (Fin n) u ^ i =
        GeneralLinearGroup.scalar (Fin n) (u ^ i) * GeneralLinearGroup.scalar (Fin n) γ⁻¹ := by
      rw [← map_pow, ← map_mul, ← map_mul, mul_comm]
    calc GeneralLinearGroup.scalar (Fin n) γ⁻¹ * a ^ i * b
        = GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b) := mul_assoc _ _ _
      _ = GeneralLinearGroup.scalar (Fin n) γ⁻¹ *
            (GeneralLinearGroup.scalar (Fin n) u ^ i * (b * a ^ i)) := by rw [h1]
      _ = (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * GeneralLinearGroup.scalar (Fin n) u ^ i) *
            (b * a ^ i) := by rw [mul_assoc]
      _ = (GeneralLinearGroup.scalar (Fin n) (u ^ i) * GeneralLinearGroup.scalar (Fin n) γ⁻¹) *
            (b * a ^ i) := by rw [e]
      _ = GeneralLinearGroup.scalar (Fin n) (u ^ i) *
            (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (b * a ^ i)) := by rw [mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin n) (u ^ i) *
            (b * (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * a ^ i)) := by
          rw [← hmv γ⁻¹ b (a ^ i)]
  · have hj3 : j ≠ 0 := hj0
    have hbj : b ^ j * a = GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) * (a * b ^ j) := by
      have := mul_pow_comm_central (fun g => hcent u g) hab j
      rw [this, map_inv, map_pow, inv_mul_cancel_left]
    refine ⟨i, j, γ, a, (u ^ j)⁻¹, hcubex, ?_, ?_, Or.inr hj3⟩
    · have hai : ∀ w : GL (Fin n) K, a ^ i * (a * w) = a * (a ^ i * w) := fun w => by
        rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_succ']
      have e : GeneralLinearGroup.scalar (Fin n) γ⁻¹ * GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) =
          GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) * GeneralLinearGroup.scalar (Fin n) γ⁻¹ := by
        rw [← map_mul, ← map_mul, mul_comm]
      calc GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j) * a
          = GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * (b ^ j * a)) := by
            simp only [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i *
              (GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) * (a * b ^ j))) := by rw [hbj]
        _ = GeneralLinearGroup.scalar (Fin n) γ⁻¹ *
              (GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) * (a ^ i * (a * b ^ j))) := by
            rw [hmv]
        _ = (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹)) *
              (a ^ i * (a * b ^ j)) := by rw [mul_assoc]
        _ = (GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) * GeneralLinearGroup.scalar (Fin n) γ⁻¹) *
              (a ^ i * (a * b ^ j)) := by rw [e]
        _ = GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) *
              (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * (a * b ^ j))) := by rw [mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) *
              (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a * (a ^ i * b ^ j))) := by rw [hai]
        _ = GeneralLinearGroup.scalar (Fin n) ((u ^ j)⁻¹) *
              (a * (GeneralLinearGroup.scalar (Fin n) γ⁻¹ * (a ^ i * b ^ j))) := by
            rw [← hmv γ⁻¹ a (a ^ i * b ^ j)]
    · exact inv_ne_one.mpr (pow_ne_one_of_lt_prime hr hu hur hj hj3)

end PairR

end CFSG.GH74.GLS.Stage2.OddAut
