module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.ComponentClassification.GHarris

theorem card_normalizer_eq_of_card_eq_seven_GL32 {P : Subgroup (GL (Fin 3) (ZMod 2))}
    (hP : Nat.card P = 7) : Nat.card (normalizer (P : Set (GL (Fin 3) (ZMod 2)))) = 21 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hs := isSimpleGroup_GL32_gh
  have hidx : P.index = 24 := by
    have h := P.card_mul_index
    rw [hP, card_GL32_gh] at h
    omega
  have hP7 : IsPGroup 7 P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  have hnd : ¬ 7 ∣ P.index := by rw [hidx]; norm_num
  have hmod := card_sylow_modEq_one 7 (GL (Fin 3) (ZMod 2))
  have hn : Nat.card (Sylow 7 (GL (Fin 3) (ZMod 2))) =
      (normalizer (P : Set (GL (Fin 3) (ZMod 2)))).index := by
    rw [Sylow.card_eq_index_normalizer (hP7.toSylow hnd)]
    congr 2
  have hdvd : (normalizer (P : Set (GL (Fin 3) (ZMod 2)))).index ∣ 24 := by
    rw [← hidx]
    exact Subgroup.index_dvd_of_le le_normalizer
  have hne1 : (normalizer (P : Set (GL (Fin 3) (ZMod 2)))).index ≠ 1 := by
    intro h1
    have hPn : P.Normal := normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h1)
    rcases hs.eq_bot_or_eq_top_of_normal P with h | h
    · rw [h, card_bot] at hP
      omega
    · rw [h, card_top, card_GL32_gh] at hP
      omega
  have h8 : (normalizer (P : Set (GL (Fin 3) (ZMod 2)))).index = 8 := by
    rw [hn] at hmod
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    interval_cases hk : (normalizer (P : Set (GL (Fin 3) (ZMod 2)))).index <;>
      first | rfl | (exfalso; revert hdvd; decide) | omega
  have h := (normalizer (P : Set (GL (Fin 3) (ZMod 2)))).card_mul_index
  rw [h8, card_GL32_gh] at h
  omega

theorem eq_top_of_two_dvd_of_seven_dvd_GL32 {H : Subgroup (GL (Fin 3) (ZMod 2))}
    (h2 : 2 ∣ Nat.card H) (h7 : 7 ∣ Nat.card H) : H = ⊤ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hH : Nat.card H ∣ 168 := card_GL32_gh ▸ Subgroup.card_subgroup_dvd_card H
  obtain ⟨P⟩ : Nonempty (Sylow 7 H) := inferInstance
  have hP : Nat.card (P : Subgroup H) = 7 := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hdvd : Nat.card (P : Subgroup H) ∣ 168 :=
      (Subgroup.card_subgroup_dvd_card (P : Subgroup H)).trans hH
    have hnd := P.not_dvd_index
    have hmul := (P : Subgroup H).card_mul_index
    rw [hk] at hdvd hmul
    rcases k with _ | _ | k
    · exfalso
      rw [pow_zero, one_mul] at hmul
      exact hnd (hmul ▸ h7)
    · rw [hk, pow_one]
    · exfalso
      have : 7 ^ 2 ∣ 168 := (pow_dvd_pow 7 (by omega : 2 ≤ k + 2)).trans hdvd
      revert this
      decide
  have hidx : (P : Subgroup H).index * 7 = Nat.card H := by
    have h := (P : Subgroup H).card_mul_index
    rw [hP] at h
    rw [← h, mul_comm]
  have hidx24 : (P : Subgroup H).index ∣ 24 := by
    obtain ⟨m, hm⟩ := hH
    refine ⟨m, ?_⟩
    have : (P : Subgroup H).index * 7 * m = 24 * 7 := by rw [hidx, ← hm]
    nlinarith
  have hmod := card_sylow_modEq_one 7 H
  have hn := Sylow.card_eq_index_normalizer P
  have hdvd : (normalizer (P : Set H)).index ∣ (P : Subgroup H).index :=
    Subgroup.index_dvd_of_le le_normalizer
  by_cases h1 : (normalizer (P : Set H)).index = 1
  ·
    exfalso
    have hPn : (P : Subgroup H).Normal :=
      normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h1)
    set P' := (P : Subgroup H).map H.subtype with hP'
    have hP'c : Nat.card P' = 7 := by
      rw [hP', card_map_of_injective H.subtype_injective, hP]
    have hle : H ≤ normalizer (P' : Set (GL (Fin 3) (ZMod 2))) := by
      have h := Subgroup.le_normalizer_map (H := (P : Subgroup H)) H.subtype
      rwa [normalizer_eq_top_iff.mpr hPn, ← MonoidHom.range_eq_map, H.range_subtype] at h
    have h21 := card_normalizer_eq_of_card_eq_seven_GL32 hP'c
    have := (Subgroup.card_dvd_of_le hle).trans h21.dvd
    have h221 : 2 ∣ 21 := h2.trans this
    revert h221
    decide
  ·
    have hn8 : (normalizer (P : Set H)).index = 8 := by
      rw [hn] at hmod
      have hd24 := hdvd.trans hidx24
      have hle := Nat.le_of_dvd (by norm_num) hd24
      unfold Nat.ModEq at hmod
      interval_cases hk : (normalizer (P : Set H)).index <;>
        first | rfl | (exfalso; revert hd24; decide) | omega
    refine eq_top_of_dvd_card_GL32 ?_
    rw [← hidx]
    rw [hn8] at hdvd
    exact Nat.mul_dvd_mul_right hdvd 7

end CFSG.ComponentClassification.GMS78
