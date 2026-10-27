module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_odd_normal_Xq {z : G} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hM : ∀ U : Subgroup G, U ≤ Mgrp z → (∀ m ∈ Mgrp z, ∀ u ∈ U, m * u * m⁻¹ ∈ U) →
      Odd (Nat.card U) → U = ⊥) :
    ∀ P : Subgroup (Xq z), P.Normal → Odd (Nat.card P) → P = ⊥ := by
  intro P hPnorm hPodd
  let n : ℕ := Nat.card P
  have hPodd' : Odd n := hPodd
  have hzM : z ∈ Mgrp z := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let c : ↥(Mgrp z) := ⟨z, hzM⟩
  have hc2 : c * c = 1 := Subtype.ext hz
  have hc1 : c ≠ 1 := fun h => hz1 (Subtype.ext_iff.mp h)
  have hc_order : orderOf c = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hc2) hc1
  have hc_center : c ∈ Subgroup.center ↥(Mgrp z) := by
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp m.2)
  have hker_eq : (piq z).ker = Subgroup.zpowers c := by
    rw [ker_piq z]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_zpow]
      exact hk
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h := congrArg Subtype.val hk
      rwa [Subgroup.coe_zpow] at h
  have hker_card : Nat.card (piq z).ker = 2 := by
    rw [hker_eq, Nat.card_zpowers, hc_order]
  have hπc : piq z c = 1 := by
    rw [← MonoidHom.mem_ker, hker_eq]
    exact Subgroup.mem_zpowers c
  let P' : Subgroup ↥(Mgrp z) := P.comap (piq z)
  have hP'norm : P'.Normal := hPnorm.comap (piq z)
  have hc_mem_P' : c ∈ P' :=
    Subgroup.mem_comap.mpr (by rw [hπc]; exact P.one_mem)
  have hP'card : Nat.card P' = 2 * n := by
    have h1 : Nat.card P' * P'.index = Nat.card ↥(Mgrp z) := Subgroup.card_mul_index P'
    have h2 : Nat.card (piq z).ker * Nat.card (Xq z) = Nat.card ↥(Mgrp z) :=
      Subgroup.card_ker_mul_card_of_surjective (piq_surjective z)
    have h3 : Nat.card P * P.index = Nat.card (Xq z) := Subgroup.card_mul_index P
    have h4 : P'.index = P.index :=
      Subgroup.index_comap_of_surjective P (piq_surjective z)
    have hPidx : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hkey : Nat.card P' * P.index = (2 * n) * P.index := by
      calc Nat.card P' * P.index = Nat.card P' * P'.index := by rw [h4]
        _ = Nat.card ↥(Mgrp z) := h1
        _ = Nat.card (piq z).ker * Nat.card (Xq z) := h2.symm
        _ = 2 * (Nat.card P * P.index) := by rw [hker_card, h3]
        _ = (2 * n) * P.index := (Nat.mul_assoc 2 (Nat.card P) P.index).symm
    exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hPidx) hkey
  let N0 : Subgroup P' := Subgroup.zpowers (⟨c, hc_mem_P'⟩ : P')
  have hN0card : Nat.card N0 = 2 := by
    show Nat.card (Subgroup.zpowers (⟨c, hc_mem_P'⟩ : P')) = 2
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hc_order]
  have hc_center_P' : (⟨c, hc_mem_P'⟩ : P') ∈ Subgroup.center P' := by
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (Subgroup.mem_center_iff.mp hc_center (↑m))
  have hN0_normal : N0.Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc_center_P')
  have hN0index : N0.index = n := by
    have h := Subgroup.card_mul_index (H := N0)
    rw [hN0card, hP'card] at h
    omega
  have hcop : Nat.Coprime (Nat.card N0) N0.index := by
    rw [hN0card, hN0index]
    exact Nat.coprime_two_left.mpr hPodd'
  haveI : N0.Normal := hN0_normal
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (G := P') (N := N0) hcop
  have hKcard : Nat.card K = n := by
    have h := hK.card_mul_card
    rw [hN0card, hP'card] at h
    omega
  let O : Subgroup ↥(Mgrp z) := K.map P'.subtype
  have hOcard : Nat.card O = n := by
    show Nat.card (K.map P'.subtype) = n
    rw [Subgroup.card_map_of_injective (K := K) (f := P'.subtype) P'.subtype_injective, hKcard]
  have hkpow : ∀ k ∈ K, k ^ n = 1 := by
    intro k hkK
    have hdvd : orderOf k ∣ n := by
      have h := Subgroup.orderOf_dvd_natCard K hkK
      rwa [hKcard] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hO_mem : ∀ u : ↥(Mgrp z), u ∈ O ↔ u ∈ P' ∧ u ^ n = 1 := by
    intro u
    constructor
    · intro hu
      have hu' : u ∈ K.map P'.subtype := hu
      rw [Subgroup.mem_map] at hu'
      obtain ⟨k, hkK, hk⟩ := hu'
      refine ⟨?_, ?_⟩
      · rw [← hk]; exact k.2
      · rw [← hk]
        calc (↑k : ↥(Mgrp z)) ^ n = ↑(k ^ n) := rfl
          _ = ↑(1 : P') := by rw [hkpow k hkK]
          _ = 1 := rfl
    · rintro ⟨huP', hun⟩
      have hxK : (⟨u, huP'⟩ : P') ∈ K := by
        have htop : (⟨u, huP'⟩ : P') ∈ N0 ⊔ K := by
          rw [hK.sup_eq_top]; exact Subgroup.mem_top _
        rw [Subgroup.mem_sup_of_normal_left] at htop
        obtain ⟨m, hmN0, k, hkK, hmk⟩ := htop
        have hm2 : m ^ 2 = 1 := by
          have hdvd : orderOf m ∣ 2 := by
            have h := Subgroup.orderOf_dvd_natCard N0 hmN0
            rwa [hN0card] at h
          exact orderOf_dvd_iff_pow_eq_one.mp hdvd
        have hmc : m ∈ Subgroup.center P' :=
          (Subgroup.zpowers_le.mpr hc_center_P') hmN0
        have hm_comm : Commute m k := (Subgroup.mem_center_iff.mp hmc k).symm
        have hk1 : k ^ n = 1 := hkpow k hkK
        have hxpow : (⟨u, huP'⟩ : P') ^ n = 1 := by
          apply Subtype.ext
          exact hun
        have hmk_pow : (m * k) ^ n = m ^ n := by
          rw [hm_comm.mul_pow, hk1, mul_one]
        have hm_pow : m ^ n = m := by
          obtain ⟨t, ht⟩ := hPodd'
          rw [ht, pow_succ, pow_mul, hm2, one_pow, one_mul]
        have hm_eq_one : m = 1 := by
          have hmn : m ^ n = 1 := by rw [← hmk_pow, hmk, hxpow]
          rwa [hm_pow] at hmn
        rw [← hmk, hm_eq_one, one_mul]
        exact hkK
      exact ⟨⟨u, huP'⟩, hxK, rfl⟩
  have hO_normal : O.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxP', hxpow⟩ := (hO_mem x).mp hx
    exact (hO_mem (g * x * g⁻¹)).mpr
      ⟨hP'norm.conj_mem x hxP' g, by rw [conj_pow, hxpow]; simp⟩
  let U : Subgroup G := O.map (Mgrp z).subtype
  have hUle : U ≤ Mgrp z := by
    intro x hx
    have hx' : x ∈ O.map (Mgrp z).subtype := hx
    rw [Subgroup.mem_map] at hx'
    obtain ⟨o, _, rfl⟩ := hx'
    exact o.2
  have hUnorm : ∀ m ∈ Mgrp z, ∀ u ∈ U, m * u * m⁻¹ ∈ U := by
    intro m hm u hu
    have hu' : u ∈ O.map (Mgrp z).subtype := hu
    rw [Subgroup.mem_map] at hu'
    obtain ⟨o, ho, rfl⟩ := hu'
    exact ⟨(⟨m, hm⟩ : ↥(Mgrp z)) * o * (⟨m, hm⟩ : ↥(Mgrp z))⁻¹,
      hO_normal.conj_mem o ho ⟨m, hm⟩, rfl⟩
  have hUodd : Odd (Nat.card U) := by
    show Odd (Nat.card (O.map (Mgrp z).subtype))
    rw [Subgroup.card_map_of_injective (Mgrp z).subtype_injective, hOcard]
    exact hPodd'
  have hUbot : U = ⊥ := hM U hUle hUnorm hUodd
  have hObot : O = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective O (Mgrp z).subtype_injective).mp hUbot
  have hn1 : n = 1 := by
    rw [← hOcard, hObot, Subgroup.card_bot]
  exact Subgroup.card_eq_one.mp hn1

end CFSG.EvenSporadicStandard.HNRecog.Harada
