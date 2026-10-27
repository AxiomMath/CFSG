module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open Subgroup

theorem card_sylow_seven_of_dvd_168 {K : Type*} [Group K] [Finite K] (hd : Nat.card K ∣ 168)
    (h7 : 7 ∣ Nat.card K) (P : Sylow 7 K) : Nat.card P = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hpos : 0 < (Nat.card K).factorization 7 :=
    Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' h7
  have hdvd : 7 ^ (Nat.card K).factorization 7 ∣ 168 := (Nat.ordProj_dvd _ _).trans hd
  have hle : (Nat.card K).factorization 7 < 2 := by
    by_contra hlt
    have : 7 ^ 2 ∣ 168 := (pow_dvd_pow 7 (not_lt.mp hlt)).trans hdvd
    omega
  have h1 : (Nat.card K).factorization 7 = 1 := by omega
  rw [P.card_eq_multiplicity, h1]
  norm_num

theorem card_normalizer_of_card_seven_simple168 {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hG : Nat.card G = 168) (Q : Subgroup G) (hQ : Nat.card Q = 7) :
    Nat.card (normalizer (Q : Set G)) = 21 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hfac : (Nat.card G).factorization 7 = 1 := by rw [hG]; decide +kernel
  let S : Sylow 7 G := Sylow.ofCard Q (by rw [hQ, hfac]; norm_num)
  have hS : (S : Subgroup G) = Q := Sylow.coe_ofCard _ _
  have hidx : Q.index = 24 := by
    have := Subgroup.index_mul_card Q
    rw [hQ, hG] at this
    omega
  have hn1 := card_sylow_modEq_one 7 G
  have hn2 : Nat.card (Sylow 7 G) ∣ 24 := by
    have := S.card_dvd_index
    rwa [hS, hidx] at this
  have hN : normalizer (S : Set G) = normalizer (Q : Set G) := by rw [← Sylow.coe_coe, hS]
  have hne : Nat.card (Sylow 7 G) ≠ 1 := by
    intro h1
    have hnorm : (normalizer (S : Set G)).index = 1 := by rw [← S.card_eq_index_normalizer, h1]
    have htop : normalizer (S : Set G) = ⊤ := Subgroup.index_eq_one.mp hnorm
    have hSn : (S : Subgroup G).Normal := normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S : Subgroup G) with h | h
    · rw [h] at hS
      rw [← hS, Subgroup.card_bot] at hQ
      omega
    · rw [h] at hS
      rw [← hS, Subgroup.card_top, hG] at hQ
      omega
  have hn3 : Nat.card (Sylow 7 G) = 8 := by
    have hle : Nat.card (Sylow 7 G) ≤ 24 := Nat.le_of_dvd (by norm_num) hn2
    generalize Nat.card (Sylow 7 G) = n at *
    interval_cases n <;> first | omega | (exfalso; revert hn1 hn2 hne; decide)
  have h8 : (normalizer (S : Set G)).index = 8 := by rw [← S.card_eq_index_normalizer, hn3]
  have := Subgroup.index_mul_card (normalizer (S : Set G))
  rw [h8, hG, hN] at this
  omega

theorem card_sylow_seven_ne_one_simple168 {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 168) {X : Subgroup G} (h14 : 14 ∣ Nat.card X) :
    Nat.card (Sylow 7 X) ≠ 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  intro h1
  haveI : Subsingleton (Sylow 7 X) := (Nat.card_eq_one_iff_unique.mp h1).1
  let P : Sylow 7 X := default
  have hPn : (P : Subgroup X).Normal := Sylow.normal_of_subsingleton P
  have hd : Nat.card X ∣ 168 := hG ▸ Subgroup.card_subgroup_dvd_card X
  have hPcard : Nat.card (P : Subgroup X) = 7 :=
    card_sylow_seven_of_dvd_168 hd (dvd_trans (by norm_num) h14) P
  have hQcard : Nat.card ((P : Subgroup X).map X.subtype) = 7 := by
    rw [Subgroup.card_subtype, hPcard]
  have hle : X ≤ normalizer (((P : Subgroup X).map X.subtype : Subgroup G) : Set G) := by
    have h1 := Subgroup.le_normalizer_map (H := (P : Subgroup X)) X.subtype
    rw [normalizer_eq_top (H := (P : Subgroup X)), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1
  have h21 := card_normalizer_of_card_seven_simple168 hG _ hQcard
  have h3 := (Subgroup.card_dvd_of_le hle).trans h21.dvd
  have h4 := h14.trans h3
  omega

theorem eq_top_of_dvd_fourteen_simple168 {G : Type*} [Group G] [Finite G] [hs : IsSimpleGroup G]
    (hG : Nat.card G = 168) {X : Subgroup G} (h14 : 14 ∣ Nat.card X) : X = ⊤ := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hd : Nat.card X ∣ 168 := hG ▸ Subgroup.card_subgroup_dvd_card X
  obtain ⟨k, hk⟩ := id h14
  have hk12 : k ∣ 12 := by
    have : 14 * k ∣ 14 * 12 := hk ▸ hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hk12 (by norm_num)
  have hkle : k ≤ 12 := Nat.le_of_dvd (by norm_num) hk12
  have hcases : k = 12 ∨ k = 4 ∨ k ∣ 6 := by
    interval_cases k <;> omega
  rcases hcases with rfl | rfl | hk6
  · exact Subgroup.eq_top_of_card_eq X (by rw [hk, hG])
  · exfalso
    have hmul := Subgroup.card_mul_index X
    rw [hk, hG] at hmul
    have h3 : X.index = 3 := by omega
    have hc := X.index_normalCore_le_factorial_index
    rcases hs.eq_bot_or_eq_top_of_normal X.normalCore with hb | ht
    · rw [hb, Subgroup.index_bot, hG, h3] at hc
      exact absurd hc (by decide)
    · have hX : X = ⊤ := top_le_iff.mp (ht ▸ X.normalCore_le)
      rw [hX, Subgroup.index_top] at h3
      exact absurd h3 (by decide)
  · exfalso
    refine card_sylow_seven_ne_one_simple168 hG h14 ?_
    have P : Sylow 7 X := default
    have hPcard : Nat.card (P : Subgroup X) = 7 :=
      card_sylow_seven_of_dvd_168 hd (dvd_trans (by norm_num) h14) P
    have hidx : (P : Subgroup X).index = 2 * k := by
      have := Subgroup.index_mul_card (P : Subgroup X)
      rw [hPcard, hk] at this
      omega
    have hn1 := card_sylow_modEq_one 7 X
    have hn2 : Nat.card (Sylow 7 X) ∣ 2 * k := hidx ▸ P.card_dvd_index
    have hn3 : Nat.card (Sylow 7 X) ∣ 12 :=
      hn2.trans (by simpa using Nat.mul_dvd_mul_left 2 hk6)
    have hle : Nat.card (Sylow 7 X) ≤ 12 := Nat.le_of_dvd (by norm_num) hn3
    unfold Nat.ModEq at hn1
    generalize Nat.card (Sylow 7 X) = n at *
    interval_cases n <;> omega

end CFSG.GF2Type.Aschbacher1976Full.HS
