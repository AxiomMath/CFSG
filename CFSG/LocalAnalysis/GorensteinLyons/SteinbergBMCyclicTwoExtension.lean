module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMFourGroupNormalizer
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup

variable {U : Type*} [Group U]

theorem inv_mul_zpow_mul_of_conj {y r : U} {j : ℤ} (h : r⁻¹ * y * r = y ^ j) (i : ℤ) :
    r⁻¹ * y ^ i * r = y ^ (j * i) := by
  have := conj_zpow (i := i) (a := r⁻¹) (b := y)
  rw [inv_inv] at this
  rw [← this, h, ← zpow_mul]

theorem principal_cyclic_two_extension_characteristic_four_group [Finite U]
    (_hU : IsPGroup 2 U) {k : ℕ} (hk : 3 ≤ k) {y : U} (hy : orderOf y = 2 ^ k)
    (_hYn : (zpowers y).Normal) (hYi : (zpowers y).index = 2)
    (hr : ∃ r : U, r ∉ zpowers y ∧ r⁻¹ * y * r = y ^ (1 + 2 ^ (k - 1))) :
    ∃ x : U, orderOf x = 2 ∧ x ∉ zpowers y ∧ closure ({y, x} : Set U) = ⊤ ∧
      x⁻¹ * y * x = y ^ (1 + 2 ^ (k - 1)) ∧
      {g : U | orderOf g = 2} = {y ^ 2 ^ (k - 1), x, x * y ^ 2 ^ (k - 1)} ∧
      ((closure ({x, y ^ 2 ^ (k - 1)} : Set U) : Subgroup U) : Set U) =
        {g | g = 1 ∨ orderOf g = 2} ∧
      (closure ({x, y ^ 2 ^ (k - 1)} : Set U)).Characteristic ∧
      CFSG.IsElementaryAbelian 2 (closure ({x, y ^ 2 ^ (k - 1)} : Set U)) ∧
      Nat.card (closure ({x, y ^ 2 ^ (k - 1)} : Set U)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  obtain ⟨r, hrY, hry⟩ := hr
  set N : ℕ := 2 ^ m with hN
  have hN0 : 0 < N := by positivity
  have hk1 : 2 ^ (m + 3 - 1) = 4 * N := by
    rw [show m + 3 - 1 = m + 2 by omega, pow_add]
    ring
  rw [hk1] at hry ⊢
  have hy8 : orderOf y = 8 * N := by
    rw [hy, pow_add]
    ring
  set z : U := y ^ (4 * N) with hz
  have hyz : ∀ i : ℤ, y ^ i = 1 ↔ (8 * N : ℤ) ∣ i := fun i => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hy8]
    push_cast
    rfl
  have hj : r⁻¹ * y * r = y ^ ((1 + 4 * N : ℕ) : ℤ) := by rw [zpow_natCast]; exact hry
  obtain ⟨c, hc⟩ := mem_zpowers_iff.mp (sq_mem_of_index_two hYi r)
  have hceven : (2 : ℤ) ∣ c := by
    have h1 : r⁻¹ * r ^ 2 * r = r ^ 2 := by group
    rw [← hc, inv_mul_zpow_mul_of_conj hj] at h1
    have h2 : y ^ (((1 + 4 * N : ℕ) : ℤ) * c - c) = 1 := by
      rw [zpow_sub, h1, mul_inv_cancel]
    rw [hyz] at h2
    have h3 : (4 * N : ℤ) * 2 ∣ (4 * N : ℤ) * c := by
      have : ((1 + 4 * N : ℕ) : ℤ) * c - c = (4 * N : ℤ) * c := by push_cast; ring
      rw [this] at h2
      exact (show (4 * N : ℤ) * 2 = 8 * N by ring) ▸ h2
    exact Int.dvd_of_mul_dvd_mul_left (by positivity) h3
  obtain ⟨c', rfl⟩ := hceven
  set i : ℤ := -c' * (1 - 2 * N) with hi
  set x : U := r * y ^ i with hx
  have hxY : x ∉ zpowers y := fun h => hrY (by
    have := mul_mem h (inv_mem (zpow_mem (mem_zpowers y) i))
    rwa [hx, mul_inv_cancel_right] at this)
  have hsq : ∀ e : ℤ, (r * y ^ e) ^ 2 = y ^ (2 * c' + (2 + 4 * N) * e) := by
    intro e
    have h1 : (r * y ^ e) ^ 2 = r ^ 2 * (r⁻¹ * y ^ e * r) * y ^ e := by
      rw [pow_two, pow_two]
      group
    rw [h1, inv_mul_zpow_mul_of_conj hj, ← hc, ← zpow_add, ← zpow_add]
    congr 1
    push_cast
    ring
  have hx2 : x ^ 2 = 1 := by
    rw [hx, hsq, hyz]
    exact ⟨N * c', by rw [hi]; ring⟩
  have hx1 : x ≠ 1 := fun h => hxY (h ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hxy : x⁻¹ * y * x = y ^ (1 + 4 * N) := by
    have : x⁻¹ * y * x = y ^ (-i) * (r⁻¹ * y * r) * y ^ i := by rw [hx]; group
    rw [this, hj, ← zpow_add, ← zpow_add, ← zpow_natCast]
    congr 1
    ring
  have hgen : closure ({y, x} : Set U) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    by_cases hg : g ∈ zpowers y
    · obtain ⟨e, rfl⟩ := mem_zpowers_iff.mp hg
      exact zpow_mem (subset_closure (Set.mem_insert _ _)) e
    · have hgx : g * x⁻¹ ∈ zpowers y :=
        (mul_mem_iff_of_index_two hYi).mpr (iff_of_false hg (fun h => hxY (by
          simpa using inv_mem h)))
      obtain ⟨e, he⟩ := mem_zpowers_iff.mp hgx
      rw [show g = g * x⁻¹ * x by group, ← he]
      exact mul_mem (zpow_mem (subset_closure (Set.mem_insert _ _)) e)
        (subset_closure (Set.mem_insert_of_mem _ rfl))
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, show 4 * N * 2 = 8 * N by ring, ← hy8, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rw [hz, Ne, ← orderOf_dvd_iff_pow_eq_one, hy8]
    intro h
    have := Nat.le_of_dvd (by positivity) h
    omega
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hzzx : x⁻¹ * z * x = z := by
    have h1 := conj_pow (a := x⁻¹) (b := y) (i := 4 * N)
    rw [inv_inv] at h1
    rw [hz, ← h1, hxy, ← pow_mul,
      show (1 + 4 * N) * (4 * N) = 4 * N + 8 * N * (2 * N) by ring, pow_add,
      pow_mul y (8 * N) (2 * N), ← hy8, pow_orderOf_eq_one, one_pow, mul_one]
  have hxz : x * z = z * x := by
    calc x * z = x * (x⁻¹ * z * x) := by rw [hzzx]
      _ = z * x := by group
  have hzY : z ∈ zpowers y := pow_mem (mem_zpowers y) _
  have hxzY : x * z ∉ zpowers y := fun h => hxY (by
    simpa using mul_mem h (inv_mem hzY))
  have hxz2 : (x * z) ^ 2 = 1 := by
    rw [(show Commute x z from hxz).mul_pow, hx2, hz2, one_mul]
  have hxz1 : x * z ≠ 1 := fun h => hxzY (h ▸ one_mem _)
  have hinv : {g : U | orderOf g = 2} = {z, x, x * z} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hg
      by_cases hgY : g ∈ zpowers y
      · left
        have := eq_of_orderOf_eq_two_of_isCyclic (X := zpowers y) (u := ⟨g, hgY⟩)
          (v := ⟨z, hzY⟩) (by rw [Subgroup.orderOf_mk, hg]) (by rw [Subgroup.orderOf_mk, hzo])
        exact congrArg Subtype.val this
      · right
        have hxg : x⁻¹ * g ∈ zpowers y :=
          (mul_mem_iff_of_index_two hYi).mpr (iff_of_false (fun h => hxY (by
            simpa using inv_mem h)) hgY)
        obtain ⟨e, he⟩ := mem_zpowers_iff.mp hxg
        have hgxe : g = r * y ^ (i + e) := by
          rw [zpow_add, ← mul_assoc, ← hx, he]
          group
        have hg2 : g ^ 2 = 1 := by rw [← hg, pow_orderOf_eq_one]
        rw [hgxe, hsq, hyz] at hg2
        have he' : (8 * N : ℤ) ∣ (2 + 4 * N) * e := by
          have h1 : 2 * c' + (2 + 4 * N) * (i + e) = 8 * N * (N * c') + (2 + 4 * N) * e := by
            rw [hi]; ring
          rw [h1] at hg2
          exact (dvd_add_right (dvd_mul_right _ _)).mp hg2
        have he4 : (4 * N : ℤ) ∣ e := by
          have h1 : (2 : ℤ) * (4 * N) ∣ 2 * ((1 + 2 * N) * e) := by
            have e1 : (2 : ℤ) * (4 * N) = 8 * N := by ring
            have e2 : (2 : ℤ) * ((1 + 2 * N) * e) = (2 + 4 * N) * e := by ring
            rw [e1, e2]
            exact he'
          have h2 := Int.dvd_of_mul_dvd_mul_left (by norm_num) h1
          have hcop : IsCoprime (4 * (N : ℤ)) (1 + 2 * N) := by
            have : (4 * (N : ℤ)) = 2 ^ (m + 2) := by
              rw [hN]
              push_cast
              rw [pow_add]
              ring
            rw [this]
            exact IsCoprime.pow_left ⟨-(N : ℤ), 1, by ring⟩
          exact hcop.dvd_of_dvd_mul_left h2
        obtain ⟨q, rfl⟩ := he4
        have hyq : y ^ ((4 * N : ℤ) * q) = z ^ q := by
          rw [hz, ← zpow_natCast, ← zpow_mul]
          push_cast
          rfl
        rcases eq_one_or_eq_of_mem_zpowers hzo (zpow_mem (mem_zpowers z) q) with h1 | h1
        · left
          rw [hgxe, zpow_add, ← mul_assoc, ← hx, hyq, h1, mul_one]
        · right
          rw [hgxe, zpow_add, ← mul_assoc, ← hx, hyq, h1]
    · rintro (rfl | rfl | rfl)
      · exact hzo
      · exact hxo
      · exact orderOf_eq_prime hxz2 hxz1
  have hxx : x * x = 1 := by rw [← pow_two, hx2]
  have hzz : z * z = 1 := by rw [← pow_two, hz2]
  have hmem : ∀ g : U, g ∈ closure ({x, z} : Set U) ↔ g = 1 ∨ g = x ∨ g = z ∨ g = x * z :=
    fun g => mem_four_iff hxx hzz hxz
  have hset : ((closure ({x, z} : Set U) : Subgroup U) : Set U) = {g | g = 1 ∨ orderOf g = 2} := by
    ext g
    rw [SetLike.mem_coe, hmem]
    have h2 : orderOf g = 2 ↔ g = z ∨ g = x ∨ g = x * z := by
      have := Set.ext_iff.mp hinv g
      simpa using this
    change _ ↔ g = 1 ∨ orderOf g = 2
    rw [h2]
    tauto
  have hchar : (closure ({x, z} : Set U)).Characteristic := by
    rw [characteristic_iff_map_le]
    intro φ
    rintro _ ⟨g, hg, rfl⟩
    rw [hset] at hg
    rw [← SetLike.mem_coe, hset]
    rcases hg with h | h
    · left
      rw [h]
      exact map_one _
    · right
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, h]
  have hEA : CFSG.IsElementaryAbelian 2 (closure ({x, z} : Set U)) := by
    have hpair : ({x, z} : Set U).Pairwise Commute := by
      rintro a (rfl | rfl) b (rfl | rfl) hab
      · exact absurd rfl hab
      · exact hxz
      · exact hxz.symm
      · exact absurd rfl hab
    have hexp : Monoid.exponent (closure ({x, z} : Set U)) ∣ 2 := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      rcases (hmem g).mp g.2 with h | h | h | h <;> rw [h]
      · exact one_pow 2
      · exact hx2
      · exact hz2
      · exact hxz2
    have := Subgroup.isMulCommutative_closure hpair
    exact ⟨hexp⟩
  have hcard : Nat.card (closure ({x, z} : Set U)) = 4 := by
    have hset' : ((closure ({x, z} : Set U) : Subgroup U) : Set U) = {1, x, z, x * z} := by
      ext g
      rw [SetLike.mem_coe, hmem]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [← SetLike.coe_sort_coe, hset', Nat.card_coe_set_eq]
    have hxz' : x ≠ z := fun h => hxY (h ▸ hzY)
    have hxzx : x * z ≠ x := fun h => hz1 (by simpa using congrArg (x⁻¹ * ·) h)
    have hxzz : x * z ≠ z := fun h => hx1 (by simpa using congrArg (· * z⁻¹) h)
    rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hx1.symm, hz1.symm, hxz1.symm⟩),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hxz', hxzx.symm⟩),
      Set.ncard_pair hxzz.symm]
  exact ⟨x, hxo, hxY, hgen, hxy, hinv, hset, hchar, hEA, hcard⟩

end CFSG.LocalAnalysis.GorensteinLyons
