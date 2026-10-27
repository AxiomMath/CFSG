module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk

open Subgroup

variable {G : Type*} [Group G]

theorem exists_diagonal {N Y : Subgroup G} {z : G} {p : ℕ} (hp : 0 < p) (hz : z ^ p = 1)
    (hzN : z ∈ normalizer (N : Set G)) (hYN : Y ≤ N)
    (hcomm : ∀ i : ℕ, 0 < i → i < p → ∀ x ∈ Y, ∀ t ∈ Y,
      z ^ i * x * (z ^ i)⁻¹ * t = t * (z ^ i * x * (z ^ i)⁻¹))
    {y : G} (hy : y ∈ Y) :
    ∃ d ∈ N ⊓ centralizer ({z} : Set G), ∀ t ∈ Y, d * t * d⁻¹ = y * t * y⁻¹ := by
  set a : ℕ → G := fun i => z ^ i * y * (z ^ i)⁻¹ with ha
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → G, r 0 = 1 ∧ ∀ k, r (k + 1) = r k * a (k + 1) :=
    ⟨fun k => Nat.rec 1 (fun k rk => rk * a (k + 1)) k, rfl, fun _ => rfl⟩
  have haN : ∀ i, a i ∈ N := fun i =>
    ((mem_normalizer_iff.mp (Subgroup.pow_mem _ hzN i) y).mp (hYN hy))
  have hrN : ∀ k, r k ∈ N := by
    intro k
    induction k with
    | zero => rw [hr0]; exact N.one_mem
    | succ k ih => rw [hrs]; exact N.mul_mem ih (haN _)
  have hrC : ∀ k, k < p → ∀ t ∈ Y, r k * t = t * r k := by
    intro k
    induction k with
    | zero => intro _ t _; rw [hr0, one_mul, mul_one]
    | succ k ih =>
      intro hk t ht
      rw [hrs, mul_assoc, show a (k + 1) * t = t * a (k + 1) from
        hcomm (k + 1) k.succ_pos hk y hy t ht, ← mul_assoc, ih (by omega) t ht, mul_assoc]
  have hza : ∀ i : ℕ, z * a i * z⁻¹ = a (i + 1) := by
    intro i
    simp only [ha, pow_succ', mul_inv_rev]
    group
  have hrz : ∀ k, z * r k * z⁻¹ = (z * y * z⁻¹)⁻¹ * r (k + 1) := by
    intro k
    induction k with
    | zero =>
      rw [hr0, hrs, hr0, one_mul]
      simp only [ha, zero_add, pow_one]
      group
    | succ k ih =>
      have e : z * r (k + 1) * z⁻¹ = (z * r k * z⁻¹) * (z * a (k + 1) * z⁻¹) := by
        rw [hrs]
        group
      rw [e, ih, hza, hrs (k + 1), mul_assoc]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have haq : a (q + 1) = y := by simp [ha, hz]
  have hryc : r q * y = y * r q := hrC q (Nat.lt_succ_self q) y hy
  refine ⟨y * r q, Subgroup.mem_inf.mpr ⟨N.mul_mem (hYN hy) (hrN q), ?_⟩, ?_⟩
  · have hzd : z * (y * r q) * z⁻¹ = y * r q := by
      have e : z * (y * r q) * z⁻¹ = (z * y * z⁻¹) * (z * r q * z⁻¹) := by group
      rw [e, hrz q, mul_inv_cancel_left, hrs q, haq, hryc]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * r q * z = z * (y * r q) * z⁻¹ * z := by rw [hzd]
      _ = z * (y * r q) := by group
  · intro t ht
    have h1 : r q * t * (r q)⁻¹ = t := by
      rw [hrC q (Nat.lt_succ_self q) t ht]
      group
    calc y * r q * t * (y * r q)⁻¹ = y * (r q * t * (r q)⁻¹) * y⁻¹ := by group
      _ = y * t * y⁻¹ := by rw [h1]

theorem mem_of_pow_mem {A : Subgroup G} {z : G} {p : ℕ} (hp : p.Prime) (hz : z ^ p = 1)
    {i : ℕ} (hi : ¬ p ∣ i) (hzi : z ^ i ∈ A) : z ∈ A := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hz1 : z = 1
  · rw [hz1]
    exact A.one_mem
  · have hord : orderOf z = p := orderOf_eq_prime hz hz1
    have hcop : i.Coprime (orderOf z) := by
      rw [hord]
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hi).symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem A hzi m

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk
