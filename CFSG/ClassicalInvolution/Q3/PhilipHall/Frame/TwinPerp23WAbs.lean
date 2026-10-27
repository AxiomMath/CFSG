module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WPerm
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.W

theorem no_free_power {Mm : Type*} [Group Mm] (Φ : Mm →* Equiv.Perm (Fin 4))
    (χ : Mm →* Equiv.Perm (Fin 5)) (p₀ : Fin 5) (hF3 : ∀ x, Φ x = 1 → χ x p₀ = p₀) (y : Mm)
    (hfree : ∀ x, ((χ y) ^ 24) x ≠ x) : False := by
  have h24 : Φ (y ^ 24) = 1 := by
    rw [map_pow]
    have := pow_card_eq_one' (G := Equiv.Perm (Fin 4)) (x := Φ y)
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
  have := hF3 (y ^ 24) h24
  rw [map_pow] at this
  exact hfree p₀ this

theorem no_order_three {Mm : Type*} [Group Mm] [Finite Mm] (Φ : Mm →* Equiv.Perm (Fin 4))
    (hΦ : Function.Surjective Φ) (Nm : Subgroup Mm) [Nm.Normal] (hNodd : Odd (Nat.card Nm))
    (χ : Mm →* Equiv.Perm (Fin 5)) (hsq : ∀ x, χ x * χ x = 1)
    (hχN : ∀ x, χ x = 1 → ∃ j : ℕ, x ^ 2 ^ j ∈ Nm) : False := by
  obtain ⟨c, hc3, hc1⟩ := exists_three_cycle
  obtain ⟨y, hy⟩ := hΦ c
  have hz : χ (y ^ 2) = 1 := by rw [map_pow, pow_two]; exact hsq y
  obtain ⟨j, hj⟩ := hχN _ hz
  set n : Mm := (y ^ 2) ^ 2 ^ j with hn
  have hΦn : Φ n = c ^ (2 * 2 ^ j) := by
    rw [hn, map_pow, map_pow, hy, ← pow_mul]
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hc'3 : (c ^ (2 * 2 ^ j)) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hc3, one_pow]
  have hc'1 : c ^ (2 * 2 ^ j) ≠ 1 := by
    intro h
    have h3 : 3 ∣ 2 * 2 ^ j := hord ▸ orderOf_dvd_of_pow_eq_one h
    have h4 : 3 ∣ 2 ^ (j + 1) := by rwa [pow_succ']
    have h5 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
    omega
  obtain ⟨g, hg2, hg1⟩ := S4_commutator _ hc'3 hc'1
  obtain ⟨m, hm⟩ := hΦ g
  set k : Mm := n * (m * n⁻¹ * m⁻¹) with hk
  have hkN : k ∈ Nm := Nm.mul_mem hj (by
    have := (inferInstance : Nm.Normal).conj_mem n⁻¹ (Nm.inv_mem hj) m
    simpa [mul_assoc] using this)
  have hΦk : Φ k = c ^ (2 * 2 ^ j) * (g * (c ^ (2 * 2 ^ j))⁻¹ * g⁻¹) := by
    rw [hk]
    simp only [map_mul, map_inv]
    rw [hΦn, hm]
  have hord2 : orderOf (Φ k) = 2 := by
    rw [hΦk]
    exact orderOf_eq_prime hg2 hg1
  have h2k : 2 ∣ orderOf k := hord2 ▸ orderOf_map_dvd Φ k
  have h2N : 2 ∣ Nat.card Nm := h2k.trans (Subgroup.orderOf_dvd_natCard Nm hkN)
  have := Nat.odd_iff.mp hNodd
  omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.W
