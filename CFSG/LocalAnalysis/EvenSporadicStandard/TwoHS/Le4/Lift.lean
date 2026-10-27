module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

section Lift

variable {L : Type*} [Group L]

theorem mk_eq_one_iff_mem_center (x : L) : (x : L ⧸ center L) = 1 ↔ x ∈ center L :=
  QuotientGroup.eq_one_iff x

theorem exists_odd_lift (hZ : ∀ z ∈ center L, z ^ 2 = 1) {q : L ⧸ center L}
    (hq : Odd (orderOf q)) : ∃ x : L, (x : L ⧸ center L) = q ∧ Odd (orderOf x) := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective q
  set d := orderOf (x₀ : L ⧸ center L) with hd
  have hd1 : (x₀ : L ⧸ center L) ^ d = 1 := pow_orderOf_eq_one _
  have hc : x₀ ^ d ∈ center L := by
    rw [← mk_eq_one_iff_mem_center, QuotientGroup.mk_pow]
    exact hd1
  have h2d : x₀ ^ (2 * d) = 1 := by rw [mul_comm, pow_mul]; exact hZ _ hc
  obtain ⟨m, hm⟩ := hq
  have hxd : (x₀ ^ (d + 1)) ^ d = 1 := by
    have : (d + 1) * d = (2 * d) * (m + 1) := by rw [hm]; ring
    rw [← pow_mul, this, pow_mul, h2d, one_pow]
  refine ⟨x₀ ^ (d + 1), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, pow_succ, hd1, one_mul]
  · exact Odd.of_dvd_nat ⟨m, hm⟩ (orderOf_dvd_of_pow_eq_one hxd)

theorem commute_of_odd_of_commute_mk (hZ : ∀ z ∈ center L, z ^ 2 = 1) {x z : L}
    (hx : Odd (orderOf x))
    (h : Commute (x : L ⧸ center L) (z : L ⧸ center L)) : Commute x z := by
  set ε : L := x * z * x⁻¹ * z⁻¹ with hε
  have hεc : ε ∈ center L := by
    rw [← mk_eq_one_iff_mem_center]
    have h1 : (x : L ⧸ center L) * z * (x : L ⧸ center L)⁻¹ * (z : L ⧸ center L)⁻¹ = 1 := by
      rw [h.eq]; group
    simpa [hε] using h1
  have hxz : x * z = ε * (z * x) := by rw [hε]; group
  have hxε : ∀ (k : ℕ) (w : L), w * ε ^ k = ε ^ k * w := fun k w =>
    (Commute.pow_right (mem_center_iff.1 hεc w : Commute w ε) k).eq
  have hpow : ∀ k : ℕ, x ^ k * z = ε ^ k * (z * x ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * z = x * (x ^ k * z) := by rw [pow_succ', mul_assoc]
        _ = x * (ε ^ k * (z * x ^ k)) := by rw [ih]
        _ = ε ^ k * (x * (z * x ^ k)) := by rw [← mul_assoc, hxε k x, mul_assoc]
        _ = ε ^ k * ((x * z) * x ^ k) := by rw [mul_assoc]
        _ = ε ^ k * ((ε * (z * x)) * x ^ k) := by rw [hxz]
        _ = ε ^ (k + 1) * (z * x ^ (k + 1)) := by
            rw [pow_succ ε k, pow_succ' x k]
            simp only [mul_assoc]
  have hod : ε ^ orderOf x = 1 := by
    have h1 := hpow (orderOf x)
    rw [pow_orderOf_eq_one, one_mul, mul_one] at h1
    have h2 : (1 : L) * z = ε ^ orderOf x * z := by rw [one_mul]; exact h1
    exact (mul_right_cancel h2).symm
  obtain ⟨m, hm⟩ := hx
  have hε2 : ε ^ 2 = 1 := hZ ε hεc
  have hε1 : ε = 1 := by
    have h3 : ε ^ (2 * m + 1) = 1 := by rw [← hm]; exact hod
    rwa [pow_succ, pow_mul, hε2, one_pow, one_mul] at h3
  show x * z = z * x
  rw [hxz, hε1, one_mul]

theorem orderOf_mk_eq_two (z : L) (hz2 : z * z ∈ center L) (hz : z ∉ center L) :
    orderOf (z : L ⧸ center L) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← QuotientGroup.mk_mul, mk_eq_one_iff_mem_center]
    exact hz2
  · rwa [Ne, mk_eq_one_iff_mem_center]

end Lift

end CFSG.EvenSporadicStandard.TwoHS
