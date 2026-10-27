module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open Subgroup

@[expose] def NoInvariantPlane {G : Type*} [Group G] (S : Subgroup G) : Prop :=
  ∀ E ≤ S, Nat.card E = 49 → ¬ normalizer (S : Set G) ≤ normalizer (E : Set G)

theorem factorization_seven_eq_three {n : ℕ} (hn : n ≠ 0) (h3 : 7 ^ 3 ∣ n) (h4 : ¬ 7 ^ 4 ∣ n) :
    n.factorization 7 = 3 := by
  have hp := Nat.prime_seven
  have a := (hp.pow_dvd_iff_le_factorization hn).1 h3
  have b : ¬ 4 ≤ n.factorization 7 := fun h => h4 ((hp.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem card_eq_sylow_seven {Γ : Type*} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    (hS : Nat.card S = 343) (hΓ : ¬ 7 ^ 4 ∣ Nat.card Γ) :
    Nat.card S = 7 ^ (Nat.card Γ).factorization 7 := by
  have h3 : 7 ^ 3 ∣ Nat.card Γ := by
    have := Subgroup.card_subgroup_dvd_card S
    rw [hS] at this
    norm_num
    exact this
  rw [factorization_seven_eq_three Nat.card_pos.ne' h3 hΓ, hS]
  norm_num

theorem false_of_index_eight {Γ : Type*} [Group Γ] [Finite Γ] {S X : Subgroup Γ}
    (hS : Nat.card S = 343) (hΓ : ¬ 7 ^ 4 ∣ Nat.card Γ) (hF3 : NoInvariantPlane S)
    (hX : normalizer (S : Set Γ) ≤ X) (hX8 : X.index = 8) : False := by
  set L := X.normalCore with hL
  have hLX : L ≤ X := X.normalCore_le
  have hidx : L.index ∣ 40320 := by
    have := X.index_normalCore_dvd_factorial_index
    rw [hX8] at this
    simpa [Nat.factorial] using this
  have hrel : L.relIndex S ∣ L.index := relIndex_dvd_index_of_normal L S
  have hmul : L.relIndex S * Nat.card ↥(L ⊓ S) = 343 := hS ▸ relIndex_mul_card L S
  have h7 : L.relIndex S ∣ 7 := by
    have h1 : L.relIndex S ∣ 343 := Dvd.intro _ hmul
    have h2 : L.relIndex S ∣ 40320 := hrel.trans hidx
    have h3 := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 343 40320 = 7 := by norm_num
    rwa [h4] at h3
  rcases (Nat.dvd_prime Nat.prime_seven).1 h7 with h | h
  ·
    rw [h, one_mul] at hmul
    have hSL : S ≤ L := by
      have : L ⊓ S = S := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hmul, hS])
      exact this ▸ inf_le_left
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hF := Sylow.normalizer_sup_eq_top' (Sylow.ofCard S (card_eq_sylow_seven hS hΓ)) hSL
    change normalizer (S : Set Γ) ⊔ L = ⊤ at hF
    have hXt : X = ⊤ := top_le_iff.1 (hF ▸ sup_le hX hLX)
    rw [hXt, Subgroup.index_top] at hX8
    exact absurd hX8 (by norm_num)
  ·
    rw [h] at hmul
    have hT : Nat.card ↥(L ⊓ S) = 49 := by omega
    apply hF3 (L ⊓ S) inf_le_right hT
    intro n hn
    rw [mem_normalizer_iff] at hn ⊢
    intro t
    constructor
    · rintro ⟨htL, htS⟩
      exact ⟨(inferInstance : L.Normal).conj_mem t htL n, (hn t).1 htS⟩
    · rintro ⟨htL, htS⟩
      refine ⟨?_, (hn t).2 htS⟩
      have := (inferInstance : L.Normal).conj_mem _ htL n⁻¹
      simpa [mul_assoc] using this

theorem NoInvariantPlane.subgroupOf {G : Type*} [Group G] {S K : Subgroup G}
    (hSK : normalizer (S : Set G) ≤ K) (h : NoInvariantPlane S) :
    NoInvariantPlane (S.subgroupOf K) := by
  intro E hES hE hNE
  have hSK' : S ≤ K := le_normalizer.trans hSK
  apply h (E.map K.subtype) ?_ ?_ ?_
  · rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hES he)
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hE]
  · have h1 : normalizer (S : Set G) = ((normalizer (S : Set G)).subgroupOf K).map K.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hSK]
    rw [h1, subgroupOf_normalizer_eq hSK']
    exact (Subgroup.map_mono hNE).trans (Subgroup.le_normalizer_map K.subtype)

theorem eq_normalizer_or_eq {G : Type*} [Group G] [Finite G] {S Y H : Subgroup G}
    (hS : Nat.card S = 343) (hY : Nat.card Y = 3753792)
    (hN : Nat.card (normalizer (S : Set G)) = 8232) (hNY : normalizer (S : Set G) ≤ Y)
    (hF3 : NoInvariantPlane S) (hNH : normalizer (S : Set G) ≤ H) (hHY : H ≤ Y) :
    H = normalizer (S : Set G) ∨ H = Y := by
  set N := normalizer (S : Set G) with hNdef
  have hSN : S ≤ N := le_normalizer
  have hSH : S ≤ H := hSN.trans hNH
  obtain ⟨m, hm⟩ := card_dvd_of_le hNH
  rw [hN] at hm
  have hm456 : m ∣ 456 := by
    have h := card_dvd_of_le hHY
    rw [hm, hY, show (3753792 : ℕ) = 8232 * 456 by norm_num] at h
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 8232)).1 h
  have hH4 : ¬ 7 ^ 4 ∣ Nat.card H := by
    intro h4
    have := h4.trans (card_dvd_of_le hHY)
    rw [hY] at this
    exact absurd this (by norm_num)
  have hm7 : m % 7 = 1 := by
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hS' : Nat.card (S.subgroupOf H) = 343 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv, hS]
    set P := Sylow.ofCard (S.subgroupOf H) (card_eq_sylow_seven hS' hH4)
    have h1 := card_sylow_modEq_one 7 H
    rw [P.card_eq_index_normalizer] at h1
    change (normalizer ((S.subgroupOf H : Subgroup H) : Set H)).index ≡ 1 [MOD 7] at h1
    rw [← subgroupOf_normalizer_eq hSH] at h1
    have h2 := (N.subgroupOf H).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, hN, hm] at h2
    have h3 : (N.subgroupOf H).index = m := by
      have := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8232) h2
      exact this
    rw [h3] at h1
    exact h1
  have hcases : m = 1 ∨ m = 8 ∨ m = 57 ∨ m = 456 := by
    have hm' : m ∈ Nat.divisors 456 := Nat.mem_divisors.2 ⟨hm456, by norm_num⟩
    have hd : Nat.divisors 456 =
        {1, 2, 3, 4, 6, 8, 12, 19, 24, 38, 57, 76, 114, 152, 228, 456} := by
      decide
    rw [hd] at hm'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
    rcases hm' with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> simp_all
  rcases hcases with rfl | rfl | rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hNH (by rw [hm, hN])).symm
  · exfalso
    have hS' : Nat.card (S.subgroupOf H) = 343 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv, hS]
    refine false_of_index_eight (Γ := H) (X := N.subgroupOf H) hS' hH4
      (hF3.subgroupOf hNH) ?_ ?_
    · rw [← subgroupOf_normalizer_eq hSH]
    · have h2 := (N.subgroupOf H).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, hN, hm] at h2
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8232) h2
  · exfalso
    have hSY : S ≤ Y := hSH.trans hHY
    have hS' : Nat.card (S.subgroupOf Y) = 343 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv, hS]
    have hY4 : ¬ 7 ^ 4 ∣ Nat.card Y := by rw [hY]; norm_num
    refine false_of_index_eight (Γ := Y) (X := H.subgroupOf Y) hS' hY4
      (hF3.subgroupOf hNY) ?_ ?_
    · rw [← subgroupOf_normalizer_eq hSY]
      exact fun x hx => Subgroup.mem_subgroupOf.2 (hNH (Subgroup.mem_subgroupOf.1 hx))
    · have h2 := (H.subgroupOf Y).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHY).toEquiv, hm, hY] at h2
      omega
  · right
    exact Subgroup.eq_of_le_of_card_ge hHY (by rw [hY, hm])

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
