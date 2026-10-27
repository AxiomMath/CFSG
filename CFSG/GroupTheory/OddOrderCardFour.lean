module

public import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.GroupTheory

theorem commute_of_odd_orderOf_of_commute_sq {G : Type*} [Group G] {g x : G}
    (hg : Odd (orderOf g)) (h : Commute (g ^ 2) x) : Commute g x := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := g) (n := 2) hg.coprime_two_right.symm
  rw [← hm]
  exact h.pow_left m

theorem conj_eq_self_of_conj_eq_mul_of_odd_orderOf {G : Type*} [Group G] {h s t : G}
    (hodd : Odd (orderOf h)) (hs : h * s * h⁻¹ = s) (hs2 : s * s = 1)
    (ht : h * t * h⁻¹ = s * t) : h * t * h⁻¹ = t := by
  have h2t : h * h * t * (h * h)⁻¹ = t := by
    calc h * h * t * (h * h)⁻¹ = h * (h * t * h⁻¹) * h⁻¹ := by group
      _ = h * (s * t) * h⁻¹ := by rw [ht]
      _ = (h * s * h⁻¹) * (h * t * h⁻¹) := by group
      _ = s * (s * t) := by rw [hs, ht]
      _ = t := by rw [← mul_assoc, hs2, one_mul]
  have hcomm2 : Commute (h ^ 2) t := by
    rw [commute_iff_eq, pow_two]
    have := congrArg (· * (h * h)) h2t
    simpa [mul_assoc] using this
  have hcomm : Commute h t := commute_of_odd_orderOf_of_commute_sq hodd hcomm2
  calc h * t * h⁻¹ = (t * h) * h⁻¹ := by rw [hcomm.eq]
    _ = t := by group

theorem conj_eq_self_of_card_eq_four_of_index_two {G : Type*} [Group G] {V : Subgroup G}
    (hV : Nat.card V = 4) {h z : G} (hhV : ∀ v ∈ V, h * v * h⁻¹ ∈ V) (hzV : z ∈ V)
    (hhz : h * z * h⁻¹ = z) (hodd : Odd (orderOf h)) (hz2 : orderOf z = 2) {t : G}
    (ht : t ∈ V) : h * t * h⁻¹ = t := by
  classical
  have hconj_zpow : ∀ k : ℤ, h * z ^ k * h⁻¹ = z ^ k := by
    intro k
    have := map_zpow (MulAut.conj h) z k
    simpa [MulAut.conj_apply, hhz] using this
  have hmem_iff : h * t * h⁻¹ ∈ Subgroup.zpowers z ↔ t ∈ Subgroup.zpowers z := by
    have hmap : (Subgroup.zpowers z).map (MulAut.conj h).toMonoidHom =
        Subgroup.zpowers z := by
      rw [MonoidHom.map_zpowers]
      have hzh : (MulAut.conj h) z = z := by simpa [MulAut.conj_apply] using hhz
      simpa using congrArg Subgroup.zpowers hzh
    have hiff : (MulAut.conj h) t ∈ (Subgroup.zpowers z).map
        (MulAut.conj h).toMonoidHom ↔ t ∈ Subgroup.zpowers z :=
      Subgroup.mem_map_iff_mem (MulAut.conj h).injective
    simpa only [MulAut.conj_apply, hmap] using hiff
  have hcard_sub : Nat.card ↥((Subgroup.zpowers z).subgroupOf V) =
      Nat.card ↥(Subgroup.zpowers z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hzV)).toEquiv
  have hidx : ((Subgroup.zpowers z).subgroupOf V).index = 2 := by
    have hmul := Subgroup.index_mul_card ((Subgroup.zpowers z).subgroupOf V)
    rw [hcard_sub, Nat.card_zpowers, hz2, hV] at hmul
    have hmul' : ((Subgroup.zpowers z).subgroupOf V).index * 2 = 2 * 2 := by
      rw [hmul]
    exact Nat.mul_right_cancel (by norm_num) hmul'
  set s : G := (h * t * h⁻¹) * t⁻¹ with hs_def
  have hmemK : (⟨h * t * h⁻¹, hhV t ht⟩ * ⟨t⁻¹, V.inv_mem ht⟩ : ↥V) ∈
      (Subgroup.zpowers z).subgroupOf V := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    constructor
    · intro ha
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      rw [Subgroup.inv_mem_iff]
      exact hmem_iff.mp ha
    · intro hb
      rw [Subgroup.mem_subgroupOf] at hb ⊢
      rw [Subgroup.inv_mem_iff] at hb
      exact hmem_iff.mpr hb
  have hs : s ∈ Subgroup.zpowers z := by
    have := Subgroup.mem_subgroupOf.mp hmemK
    rw [hs_def]
    simpa using this
  have hs_fix : h * s * h⁻¹ = s := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
    rw [← hk, hconj_zpow k]
  have hs2 : s * s = 1 := by
    have hdvd : orderOf s ∣ 2 := by
      rw [← hz2]
      exact orderOf_dvd_of_mem_zpowers hs
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have ht' : h * t * h⁻¹ = s * t := by
    rw [hs_def]
    group
  exact conj_eq_self_of_conj_eq_mul_of_odd_orderOf hodd hs_fix hs2 ht'

theorem conj_eq_self_of_card_eq_four {G : Type*} [Group G] {V : Subgroup G}
    (hV : Nat.card V = 4) {h z : G} (hhV : ∀ v ∈ V, h * v * h⁻¹ ∈ V) (hzV : z ∈ V)
    (hz1 : z ≠ 1) (hhz : h * z * h⁻¹ = z) (hodd : Odd (orderOf h)) {t : G} (ht : t ∈ V) :
    h * t * h⁻¹ = t := by
  classical
  have hVfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  have hzdvd : orderOf z ∣ 4 := by
    simpa [hV] using Subgroup.orderOf_dvd_natCard V hzV
  have hz1' : orderOf z ≠ 1 := fun h1 => hz1 (orderOf_eq_one_iff.mp h1)
  have hcases : orderOf z = 1 ∨ orderOf z = 2 ∨ orderOf z = 4 := by
    have hzdvd' : orderOf z ∣ 2 ^ 2 := by simpa using hzdvd
    obtain ⟨k, _hk, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hzdvd'
    interval_cases k <;> simp_all
  rcases hcases with h1 | h2 | h4
  · exact absurd h1 hz1'
  · exact conj_eq_self_of_card_eq_four_of_index_two hV hhV hzV hhz hodd h2 ht
  · have hconj_zpow : ∀ k : ℤ, h * z ^ k * h⁻¹ = z ^ k := by
      intro k
      have := map_zpow (MulAut.conj h) z k
      simpa [MulAut.conj_apply, hhz] using this
    have hEq : Subgroup.zpowers z = V :=
      @Subgroup.eq_of_le_of_card_ge G _ (Subgroup.zpowers z) V hVfin
        (Subgroup.zpowers_le.mpr hzV) (by rw [hV, Nat.card_zpowers, h4])
    have ht' : t ∈ Subgroup.zpowers z := by rwa [hEq]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht'
    calc h * t * h⁻¹ = h * z ^ k * h⁻¹ := by rw [← hk]
      _ = z ^ k := hconj_zpow k
      _ = t := hk

end CFSG.GroupTheory
