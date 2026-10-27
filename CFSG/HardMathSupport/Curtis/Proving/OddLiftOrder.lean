module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Factorization.Basic

public section

namespace CFSG.HardMathSupport.Curtis.Proving

theorem exists_odd_order_lift {G Q : Type} [Group G] [Finite G] [Group Q] (φ : G →* Q)
    (l : G) {r : ℕ} (hr : Odd r) (hz : φ l ^ r = 1) :
    ∃ t : G, φ t = φ l ∧ Odd (orderOf t) := by
  have hn : orderOf l ≠ 0 := (orderOf_pos l).ne'
  obtain ⟨k, m, hm, hnk⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : Nat.Coprime (2 ^ k) m := (Nat.coprime_two_left.2 hm).pow_left k
  obtain ⟨e, he1, he2⟩ := Nat.chineseRemainder hcop 1 0
  have hm_e : m ∣ e := (Nat.modEq_zero_iff_dvd).1 he2
  have h2k : (2 ^ k : ℤ) ∣ (e : ℤ) - 1 := by
    have := Nat.modEq_iff_dvd.1 he1.symm
    simpa using this
  have h2 : (2 ^ k : ℤ) ∣ 1 - (e : ℤ) := by
    have := dvd_neg.2 h2k
    rwa [neg_sub] at this
  have hlpow : l ^ (e * 2 ^ k) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hnk, mul_comm e]
    exact mul_dvd_mul_left (2 ^ k) hm_e
  have hx2 : (φ l ^ e) ^ (2 ^ k) = 1 := by
    rw [← map_pow, ← map_pow, ← pow_mul, hlpow, map_one]
  have hxr : (φ l ^ e) ^ r = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have hgcd : Nat.gcd (2 ^ k) r = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.coprime_two_left.2 hr).pow_left k)
  have hx1 : φ l ^ e = 1 := by
    have : (φ l ^ e) ^ Nat.gcd (2 ^ k) r = 1 := pow_gcd_eq_one.2 ⟨hx2, hxr⟩
    rwa [hgcd, pow_one] at this
  refine ⟨l * (l ^ e)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, map_pow, hx1, inv_one, mul_one]
  · have ht : l * (l ^ e)⁻¹ = l ^ ((1 : ℤ) - (e : ℤ)) := by
      rw [sub_eq_add_neg, zpow_add, zpow_one, zpow_neg, zpow_natCast]
    have hdiv : ((orderOf l : ℕ) : ℤ) ∣ (1 - (e : ℤ)) * (m : ℤ) := by
      rw [hnk]
      push_cast
      exact mul_dvd_mul_right h2 _
    have hpow1 : l ^ ((1 - (e : ℤ)) * (m : ℤ)) = 1 := orderOf_dvd_iff_zpow_eq_one.1 hdiv
    have htm : (l * (l ^ e)⁻¹) ^ m = 1 := by
      rw [ht, ← zpow_natCast, ← zpow_mul]
      exact hpow1
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one htm)

end CFSG.HardMathSupport.Curtis.Proving

end
