module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group
public import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.GroupTheory

private theorem conj_zpow_eq_inv {G : Type*} [Group G] {b k : G} (hbk : k * b * k⁻¹ = b⁻¹)
    (m : ℤ) : k * b ^ m * k⁻¹ = (b ^ m)⁻¹ := by
  rw [← conj_zpow, hbk, inv_zpow]

theorem zpow_eq_one_of_odd_orderOf {G : Type*} [Group G] {b : G} (hb : Odd (orderOf b))
    {m : ℤ} (h : b ^ (2 * m) = 1) : b ^ m = 1 := by
  have hdvd : orderOf (b ^ m) ∣ orderOf b :=
    orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers b m)
  have hodd : Odd (orderOf (b ^ m)) := hb.of_dvd_nat hdvd
  have h2 : orderOf (b ^ m) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two, ← zpow_add, show m + m = 2 * m by rw [two_mul]]
    exact h
  have hne : orderOf (b ^ m) ≠ 2 := by
    intro h
    rw [h] at hodd
    exact hodd.not_two_dvd_nat dvd_rfl
  exact orderOf_eq_one_iff.mp ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_right hne)

theorem mem_closure_pair_of_conj_eq_inv {G : Type*} [Group G] {b k x : G}
    (hk2 : k * k = 1) (hbk : k * b * k⁻¹ = b⁻¹)
    (hx : x ∈ Subgroup.closure ({b, k} : Set G)) :
    ∃ m : ℤ, x = b ^ m ∨ x = b ^ m * k := by
  have htwo : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
  have hkpow : ∀ n : ℤ, k ^ n = 1 ∨ k ^ n = k := by
    intro n
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' n
    · left
      rw [zpow_mul, htwo, zpow_natCast, pow_two, hk2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, htwo, zpow_natCast, pow_two, hk2, one_zpow, one_mul, zpow_one]
  have hsup : Subgroup.closure ({b, k} : Set G) = Subgroup.zpowers b ⊔ Subgroup.zpowers k := by
    rw [← Set.singleton_union, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure b,
      ← Subgroup.zpowers_eq_closure k]
  have hk_mem : k ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (k * b * k⁻¹) = Subgroup.zpowers b
    rw [hbk, Subgroup.zpowers_inv]
  have hnorm : Subgroup.zpowers k ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    Subgroup.zpowers_le.mpr hk_mem
  rw [hsup, TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := Subgroup.zpowers b)
    (K := Subgroup.zpowers k) hnorm] at hx
  obtain ⟨y, hy, t, ht, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  rcases hkpow n with hn | hn
  · exact ⟨m, Or.inl (by rw [hn, mul_one])⟩
  · exact ⟨m, Or.inr (by rw [hn])⟩

theorem mem_zpowers_right_of_mem_closure_pair_of_conj_eq_inv {G : Type*} [Group G] {b k x : G}
    (hk2 : k * k = 1) (hbk : k * b * k⁻¹ = b⁻¹) (hb : Odd (orderOf b))
    (hx : x ∈ Subgroup.closure ({b, k} : Set G)) (hcomm : x * k = k * x) :
    x ∈ Subgroup.zpowers k := by
  have hk1 : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
  obtain ⟨m, hm | hm⟩ := mem_closure_pair_of_conj_eq_inv hk2 hbk hx
  · subst hm
    have h1 : b ^ m = (b ^ m)⁻¹ := by
      calc b ^ m = b ^ m * (k * k) := by rw [hk2, mul_one]
        _ = (b ^ m * k) * k := by group
        _ = (k * b ^ m) * k := by rw [hcomm]
        _ = k * b ^ m * k := by rw [mul_assoc]
        _ = k * b ^ m * k⁻¹ := by rw [hk1]
        _ = (b ^ m)⁻¹ := conj_zpow_eq_inv hbk m
    have h2 : b ^ (2 * m) = 1 := by
      calc b ^ (2 * m) = b ^ m * b ^ m := by
            rw [show (2 : ℤ) * m = m + m by exact two_mul m, zpow_add]
        _ = (b ^ m)⁻¹ * b ^ m := by nth_rewrite 1 [h1]; rfl
        _ = 1 := inv_mul_cancel (b ^ m)
    rw [zpow_eq_one_of_odd_orderOf hb h2]
    exact Subgroup.one_mem (Subgroup.zpowers k)
  · subst hm
    have h1 : b ^ m = (b ^ m)⁻¹ := by
      calc b ^ m = (b ^ m * k) * k := by rw [mul_assoc, hk2, mul_one]
        _ = k * (b ^ m * k) := hcomm
        _ = k * b ^ m * k := by rw [mul_assoc]
        _ = k * b ^ m * k⁻¹ := by rw [hk1]
        _ = (b ^ m)⁻¹ := conj_zpow_eq_inv hbk m
    have h2 : b ^ (2 * m) = 1 := by
      calc b ^ (2 * m) = b ^ m * b ^ m := by
            rw [show (2 : ℤ) * m = m + m by exact two_mul m, zpow_add]
        _ = (b ^ m)⁻¹ * b ^ m := by nth_rewrite 1 [h1]; rfl
        _ = 1 := inv_mul_cancel (b ^ m)
    rw [zpow_eq_one_of_odd_orderOf hb h2, one_mul]
    exact Subgroup.mem_zpowers k

theorem mem_zpowers_left_of_mem_closure_pair_of_conj_eq_inv {G : Type*} [Group G] {b k x : G}
    (hk2 : k * k = 1) (hbk : k * b * k⁻¹ = b⁻¹) (hb2 : b ^ 2 ≠ 1)
    (hx : x ∈ Subgroup.closure ({b, k} : Set G)) (hcomm : x * b = b * x) :
    x ∈ Subgroup.zpowers b := by
  have hk1 : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
  obtain ⟨m, hm | hm⟩ := mem_closure_pair_of_conj_eq_inv hk2 hbk hx
  · rw [hm]
    exact Subgroup.zpow_mem_zpowers b m
  · exfalso
    subst hm
    have hbm : b * b ^ m = b ^ m * b := by rw [← zpow_one_add, add_comm, zpow_add_one]
    have hkb : k * b = b * k := by
      have h1 : b ^ m * (k * b) = b ^ m * (b * k) := by
        calc b ^ m * (k * b) = (b ^ m * k) * b := by group
          _ = b * (b ^ m * k) := hcomm
          _ = (b * b ^ m) * k := by rw [mul_assoc]
          _ = (b ^ m * b) * k := by rw [hbm]
          _ = b ^ m * (b * k) := by rw [mul_assoc]
      exact mul_left_cancel h1
    have hb_eq : b = b⁻¹ := by
      have h : k * b * k⁻¹ = b := by rw [hkb, hk1, mul_assoc, hk2, mul_one]
      rw [← hbk, h]
    exact hb2 (by rw [pow_two]; exact eq_inv_iff_mul_eq_one.mp hb_eq)

end CFSG.GroupTheory
