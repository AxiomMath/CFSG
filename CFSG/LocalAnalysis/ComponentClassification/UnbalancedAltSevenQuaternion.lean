module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenAlternating
public import CFSG.LocalAnalysis.ComponentInitial.PerfectRankOneSylow
public import CFSG.CharacterTheory.Semidihedral.QuaternionDoubleCoverUniqueness

public section

namespace CFSG.ComponentClassification.UnbalancedAltSeven

open Equiv Equiv.Perm Subgroup

variable {E : Type*} [Group E]

theorem mem_zpowers_of_orderOf_eq_two {z : E} (hz : orderOf z = 2) {g : E} :
    g ∈ zpowers z ↔ g = 1 ∨ g = z := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 h
    rw [← zpow_mod_orderOf, hz, Nat.cast_ofNat]
    rcases Int.emod_two_eq k with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem eq_or_eq_mul_of_map_eq {G : Type*} [Group G] {z : E} (hz : orderOf z = 2)
    {π : E →* G} (hker : π.ker = zpowers z) {y w : E} (h : π y = π w) :
    y = w ∨ y = w * z := by
  have hm : w⁻¹ * y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [hker, mem_zpowers_of_orderOf_eq_two hz] at hm
  rcases hm with hm | hm
  · left
    rw [inv_mul_eq_one] at hm
    exact hm.symm
  · right
    rw [inv_mul_eq_iff_eq_mul] at hm
    exact hm

theorem sq_eq_of_map_eq {G : Type*} [Group G] {z : E} (hzc : z ∈ center E)
    (hz : orderOf z = 2) {π : E →* G} (hker : π.ker = zpowers z) {y w : E} (h : π y = π w) :
    y ^ 2 = w ^ 2 := by
  rcases eq_or_eq_mul_of_map_eq hz hker h with rfl | rfl
  · rfl
  · have hzz : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
    have hcomm : Commute w z := mem_center_iff.1 hzc w
    rw [hcomm.mul_pow, hzz, mul_one]

section Cover

variable {z : E} {π : E →* alternatingGroup (Fin 7)}

theorem card_eq_of_cover (hz : orderOf z = 2) (hπ : Function.Surjective π)
    (hker : π.ker = zpowers z) : Nat.card E = 5040 := by
  rw [card_eq_card_quotient_mul_card_subgroup π.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hker,
    Nat.card_zpowers, hz, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem eq_of_orderOf_eq_two_of_lift (hzc : z ∈ center E) (hz : orderOf z = 2)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers z) {x : E} (hx : x ^ 2 = z)
    (hxπ : π x = tZero) {y : E} (hy : orderOf y = 2) : y = z := by
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  by_cases h1 : π y = 1
  · have hyk : y ∈ π.ker := h1
    rw [hker, mem_zpowers_of_orderOf_eq_two hz] at hyk
    rcases hyk with rfl | rfl
    · rw [orderOf_one] at hy
      exact absurd hy (by norm_num)
    · rfl
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ht : orderOf (π y) = 2 := orderOf_eq_prime (by rw [← map_pow, hy2, map_one]) h1
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_tZero ht)
    obtain ⟨g, rfl⟩ := hπ c
    have hmap : π y = π (g * x * g⁻¹) := by rw [← hc, map_mul, map_mul, map_inv, hxπ]
    have hsq := sq_eq_of_map_eq hzc hz hker hmap
    rw [hy2, conj_pow, hx, mem_center_iff.1 hzc g, mul_inv_cancel_right] at hsq
    rw [← hsq, orderOf_one] at hz
    exact absurd hz (by norm_num)

theorem isPerfect_of_lift (hzc : z ∈ center E) (hz : orderOf z = 2)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers z) {x : E} (hx : x ^ 2 = z)
    (hxπ : π x = tZero) : Group.IsPerfect E := by
  have hmap : (commutator E).map π = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hπ, ← _root_.commutator_def,
      commutator_alternatingGroup_eq_top (by simp)]
  have hzD : z ∈ commutator E := by
    obtain ⟨d, hd, hdπ⟩ := mem_map.1 (hmap ▸ mem_top tZero : tZero ∈ (commutator E).map π)
    have hsq := sq_eq_of_map_eq hzc hz hker (hdπ.trans hxπ.symm)
    rw [hx] at hsq
    rw [← hsq]
    exact pow_mem hd 2
  refine ⟨eq_top_iff.2 fun g _ => ?_⟩
  obtain ⟨d, hd, hdπ⟩ := mem_map.1 (hmap ▸ mem_top (π g) : π g ∈ (commutator E).map π)
  rcases eq_or_eq_mul_of_map_eq hz hker hdπ.symm with rfl | rfl
  · exact hd
  · exact mul_mem hd hzD

theorem center_eq_of_cover (hzc : z ∈ center E) (hπ : Function.Surjective π)
    (hker : π.ker = zpowers z) : center E = zpowers z := by
  refine le_antisymm (fun g hg => ?_) (zpowers_le.2 hzc)
  have hcen : π g ∈ center (alternatingGroup (Fin 7)) := by
    rw [mem_center_iff] at hg ⊢
    intro h
    obtain ⟨k, rfl⟩ := hπ h
    rw [← map_mul, ← map_mul, hg k]
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hcen
  rw [← hker]
  exact hcen

theorem pRank_le_one_of_unique [Finite E] {z : E} (hz : orderOf z = 2)
    (huniq : ∀ y : E, orderOf y = 2 → y = z) : CFSG.pRank 2 E ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  apply CFSG.SectionRank.pRank_le (by norm_num)
  intro A _ hA
  have hle : A ≤ zpowers z := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact one_mem _
    · rw [huniq y (orderOf_eq_prime (hA.2 y hy) hy1)]
      exact mem_zpowers z
  calc Nat.card A ≤ Nat.card (zpowers z) := card_le_of_le hle
    _ = 2 ^ 1 := by rw [Nat.card_zpowers, hz, pow_one]

theorem sylow_quaternion_of_lift [Finite E] (hzc : z ∈ center E) (hz : orderOf z = 2)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers z) {x : E} (hx : x ^ 2 = z)
    (hxπ : π x = tZero) (S : Sylow 2 E) :
    Nonempty (S ≃* QuaternionGroup 4) ∧ Nat.card S = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect E := isPerfect_of_lift hzc hz hπ hker hx hxπ
  have hcard := card_eq_of_cover hz hπ hker
  have heven : Even (Nat.card E) := by rw [hcard]; decide
  have hrank := pRank_le_one_of_unique hz fun y hy =>
    eq_of_orderOf_eq_two_of_lift hzc hz hπ hker hx hxπ hy
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.perfect_rank_one_Sylow_quaternion heven hrank S
  have hS : Nat.card S = 2 ^ n :=
    (Nat.card_congr e.toEquiv).trans
      (CFSG.Semidihedral.QuaternionDoubleCoverUniqueness.quaternion_natCard n hn)
  have hdvd : 2 ^ n ∣ 5040 := by
    rw [← hS, ← hcard]
    exact card_subgroup_dvd_card _
  have h16 : 2 ^ 4 ∣ 2 ^ n := by
    rw [← hS]
    exact S.pow_dvd_card_of_pow_dvd_card (by rw [hcard]; decide)
  have hn4 : n = 4 := by
    have h1 : 4 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h16
    have h2 : n ≤ 4 := by
      by_contra h
      have h5 : 2 ^ 5 ∣ 5040 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      exact absurd h5 (by decide)
    omega
  subst hn4
  exact ⟨⟨e⟩, hS⟩

theorem cover_of_lift [Finite E] (hzc : z ∈ center E) (hz : orderOf z = 2)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers z) {x : E} (hx : x ^ 2 = z)
    (hxπ : π x = tZero) :
    Nat.card E = 5040 ∧ Group.IsPerfect E ∧ center E = zpowers z ∧
      Nonempty (E ⧸ center E ≃* alternatingGroup (Fin 7)) ∧
      (∀ y : E, orderOf y = 2 → y = z) ∧
      ∀ S : Sylow 2 E, Nonempty (S ≃* QuaternionGroup 4) ∧ Nat.card S = 16 := by
  have hcen := center_eq_of_cover hzc hπ hker
  refine ⟨card_eq_of_cover hz hπ hker, isPerfect_of_lift hzc hz hπ hker hx hxπ, hcen,
    ⟨(QuotientGroup.quotientMulEquivOfEq (hcen.trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩,
    fun y hy => eq_of_orderOf_eq_two_of_lift hzc hz hπ hker hx hxπ hy,
    sylow_quaternion_of_lift hzc hz hπ hker hx hxπ⟩

end Cover

end CFSG.ComponentClassification.UnbalancedAltSeven
