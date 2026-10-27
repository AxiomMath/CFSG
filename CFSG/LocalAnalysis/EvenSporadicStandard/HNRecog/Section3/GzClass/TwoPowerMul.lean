module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_two_pow_orderOf_mul_of_mem {G : Type*} [Group G] {K Q : Subgroup G}
    (hQ2 : IsPGroup 2 ↥Q) (hQn : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) {x y : G} (hxK : x ∈ K)
    (hx2 : x ^ 2 = 1) (hyQ : y ∈ Q) : ∃ k : ℕ, orderOf (x * y) = 2 ^ k := by
  have hx_mul : x * x = 1 := by simpa [pow_two] using hx2
  have hx_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx_mul
  have hmem : x * y * x⁻¹ ∈ Q := hQn x hxK y hyQ
  have hsq : (x * y) ^ 2 = (x * y * x⁻¹) * y := by
    rw [pow_two, hx_inv]
    group
  have hsqQ : (x * y) ^ 2 ∈ Q := by
    rw [hsq]
    exact Q.mul_mem hmem hyQ
  obtain ⟨j, hj⟩ := hQ2.exists_orderOf_eq_pow ⟨(x * y) ^ 2, hsqQ⟩
  have horder2 : orderOf ((x * y) ^ 2) = 2 ^ j := by
    simpa using (Subgroup.orderOf_coe (⟨(x * y) ^ 2, hsqQ⟩ : ↥Q)).trans hj
  have hdvd : orderOf (x * y) ∣ 2 ^ (j + 1) := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_succ']
    calc (x * y) ^ (2 * 2 ^ j) = ((x * y) ^ 2) ^ (2 ^ j) := pow_mul (x * y) 2 (2 ^ j)
      _ = 1 := by
        rw [← horder2]
        exact pow_orderOf_eq_one _
  obtain ⟨k, _hk, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
