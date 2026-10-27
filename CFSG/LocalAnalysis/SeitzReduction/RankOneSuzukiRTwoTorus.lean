module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G] {K : Type*} [Field K]

namespace SzRootCoords

variable {T₁ : Subgroup G} {a : ℕ} {d : G} {u v : G → K} {κ : K}

theorem pow (hc : SzRootCoords T₁ a d u v κ) (k : ℕ) :
    SzRootCoords T₁ a (d ^ k) u v (κ ^ k) := by
  have key : ∀ x ∈ T₁, (d ^ k)⁻¹ * x * d ^ k ∈ T₁ ∧
      u ((d ^ k)⁻¹ * x * d ^ k) = κ ^ k * u x ∧
      (u x = 0 → v ((d ^ k)⁻¹ * x * d ^ k) = (κ ^ k) ^ (2 ^ (a + 1) + 1) * v x) := by
    induction k with
    | zero => intro x hx; simp [hx]
    | succ k ih =>
      intro x hx
      obtain ⟨h1, h2, h3⟩ := ih x hx
      have e : (d ^ (k + 1))⁻¹ * x * d ^ (k + 1) = d⁻¹ * ((d ^ k)⁻¹ * x * d ^ k) * d := by
        rw [pow_succ]
        group
      rw [e]
      refine ⟨hc.conj_mem _ h1, ?_, fun hu => ?_⟩
      · rw [hc.conj_u _ h1, h2, pow_succ κ k]
        ring
      · have hu' : u ((d ^ k)⁻¹ * x * d ^ k) = 0 := by rw [h2, hu, mul_zero]
        rw [hc.conj_v _ h1 hu', h3 hu, pow_succ κ k, mul_pow]
        ring
  exact ⟨hc.mul, hc.inj, hc.surj, fun x hx => (key x hx).1, fun x hx => (key x hx).2.1,
    fun x hx hu => (key x hx).2.2 hu⟩

theorem generator_pow_two_pow [Finite K] [CharP K 2] {μ : K}
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) (N : ℕ) :
    ∀ w : K, w ≠ 0 → ∃ m : ℕ, (μ ^ 2 ^ N) ^ m = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (fun z : K => z ^ 2 ^ N) := by
    intro z z' h
    have h1 : (z - z') ^ 2 ^ N = 0 := by
      rw [sub_pow_char_pow]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero N two_ne_zero)).mp h1)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro w hw
  obtain ⟨w₀, rfl⟩ := hsurj w
  have hw₀ : w₀ ≠ 0 := by
    rintro rfl
    exact hw (zero_pow (pow_ne_zero N two_ne_zero))
  obtain ⟨m, hm⟩ := hμ w₀ hw₀
  refine ⟨m, ?_⟩
  change (μ ^ 2 ^ N) ^ m = w₀ ^ 2 ^ N
  rw [← hm, ← pow_mul, ← pow_mul, mul_comm]

theorem exists_odd_pow [Finite G] [Finite K] [CharP K 2] (hc : SzRootCoords T₁ a d u v κ)
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) :
    ∃ k : ℕ, Odd (orderOf (d ^ k)) ∧ SzRootCoords T₁ a (d ^ k) u v (κ ^ k) ∧
      (∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ k) ^ m = w) ∧
      ∀ w : K, w ≠ 0 → ∃ m : ℕ, ((κ ^ k) ^ (2 ^ (a + 1) + 1)) ^ m = w := by
  set N := orderOf d with hN
  have hN0 : N ≠ 0 := (orderOf_pos d).ne'
  obtain ⟨s, m, hm, hNsm⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  have hsN : s ≤ N := by
    have h1 : 2 ^ s ≤ N := by
      rw [hNsm]
      exact Nat.le_mul_of_pos_right _ hm.pos
    exact (Nat.lt_two_pow_self).le.trans h1
  refine ⟨2 ^ N, ?_, hc.pow _, generator_pow_two_pow hκ N, ?_⟩
  · have h1 : (d ^ 2 ^ N) ^ m = 1 := by
      have e : 2 ^ N * m = N * 2 ^ (N - s) := by
        calc 2 ^ N * m = 2 ^ (s + (N - s)) * m := by rw [Nat.add_sub_cancel' hsN]
          _ = 2 ^ s * m * 2 ^ (N - s) := by rw [pow_add]; ring
          _ = N * 2 ^ (N - s) := by rw [← hNsm]
      rw [← pow_mul, e, pow_mul, hN, pow_orderOf_eq_one, one_pow]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · have e : (κ ^ 2 ^ N) ^ (2 ^ (a + 1) + 1) = (κ ^ (2 ^ (a + 1) + 1)) ^ 2 ^ N := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e]
    exact generator_pow_two_pow hμ N

end SzRootCoords

end CFSG.SeitzReduction.RankOne
