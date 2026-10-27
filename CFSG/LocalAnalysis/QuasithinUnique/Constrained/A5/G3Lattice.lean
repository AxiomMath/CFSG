module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Direct
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem not_isDelta5_of_overgroups {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X)
    {t₂ : ℕ} (ht₂ : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → Nat.card T = t₂)
    (hover : ∀ T Y : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Y → Y = ⊤ ∨
      (Nat.card Y = 15 * t₂ → ∃ q : ℕ, q * 64 < t₂ ∧ ∀ (N : Subgroup ↥Y) [N.Normal],
        IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ q))
    {T B : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hne : B ≠ ⊤)
    (hTB : T ≤ Subgroup.normalizer (B : Set X)) : ¬ IsDelta5Group ↥B := by
  intro hD
  classical
  have h960 : Nat.card ↥B = 960 := hD.card
  set Y : Subgroup X := B ⊔ T with hY
  have hBY : B ≤ Y := le_sup_left
  have hTY : T ≤ Y := le_sup_right
  have hYN : Y ≤ Subgroup.normalizer (B : Set X) := sup_le Subgroup.le_normalizer hTB
  rcases hover T Y hT hTY with htop | hq
  ·
    have hnorm : B.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hg : g ∈ Subgroup.normalizer (B : Set X) := hYN (htop ▸ Subgroup.mem_top g)
      exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h | h
    · rw [h, Subgroup.card_bot] at h960
      omega
    · exact hne h
  ·
    set N : Subgroup ↥Y := B.subgroupOf Y with hN
    have hNn : N.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBY).mpr hYN
    have hTp : IsPGroup 2 ↥(T.subgroupOf Y) :=
      hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
    have hsup : N ⊔ T.subgroupOf Y = ⊤ := by
      rw [hN, ← Subgroup.subgroupOf_sup hBY hTY, ← hY, Subgroup.subgroupOf_self]
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' N).comp (T.subgroupOf Y).subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
      have h1 : (N ⊔ T.subgroupOf Y).map (QuotientGroup.mk' N) = ⊤ := by
        rw [hsup]
        exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
      exact h1
    have hQp : IsPGroup 2 (↥Y ⧸ N) := IsPGroup.of_surjective (hTp) _ hsurj
    obtain ⟨j, hj⟩ := hQp.exists_card_eq
    have hNcard : Nat.card N = 960 := by
      rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv, h960]
    have hYcard : Nat.card ↥Y = 2 ^ j * 960 := by
      rw [← hj, ← hNcard]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup N)
    have ht2Y : t₂ ∣ Nat.card ↥Y := by
      rw [← ht₂ T hT]
      exact Subgroup.card_dvd_of_le hTY
    obtain ⟨s, hs⟩ := hT.2.1.exists_card_eq
    rw [ht₂ T hT] at hs
    have hid : 2 ^ j * 960 = 2 ^ (6 + j) * 15 := by rw [pow_add]; ring
    have hsj : s = 6 + j := by
      have h1 : 2 ^ s ∣ 2 ^ (6 + j) * 15 := by
        rw [← hs, ← hid, ← hYcard]
        exact ht2Y
      have h2 : 2 ^ s ∣ 2 ^ (6 + j) :=
        Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left s (by norm_num : Nat.Coprime 2 15))
          h1
      have h3 : s ≤ 6 + j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
      have h4 : 2 ^ (6 + j) ∣ Nat.card X := by
        have h5 : 2 ^ (6 + j) ∣ Nat.card ↥Y := by
          rw [hYcard, show 2 ^ (6 + j) = 2 ^ j * 64 by rw [pow_add]; ring]
          exact mul_dvd_mul_left _ (by norm_num)
        exact h5.trans (Subgroup.card_subgroup_dvd_card Y)
      have hidx : Nat.card X = t₂ * T.index := by
        rw [← ht₂ T hT]
        exact (Subgroup.card_mul_index T).symm
      have hodd : ¬ 2 ∣ T.index := by
        have h1 : (T.subgroupOf (⊤ : Subgroup X)).index = T.index := Subgroup.relIndex_top_right T
        have := hT.2.2
        rwa [h1] at this
      have hcop : Nat.Coprime (2 ^ (6 + j)) T.index :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
      have h6 : 2 ^ (6 + j) ∣ 2 ^ s := by
        rw [hidx, hs] at h4
        exact hcop.dvd_of_dvd_mul_right h4
      have h7 : 6 + j ≤ s := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h6
      omega
    have ht2 : t₂ = 2 ^ (6 + j) := by rw [hs, hsj]
    have hY15 : Nat.card ↥Y = 15 * t₂ := by
      rw [hYcard, ht2, hid]
      ring
    obtain ⟨q, hq64, hqN⟩ := hq hY15
    have hle := hqN N hQp
    rw [hj] at hle
    have : 2 ^ j * 64 ≤ q * 64 := Nat.mul_le_mul_right 64 hle
    have h64 : t₂ = 2 ^ j * 64 := by rw [ht2, pow_add]; ring
    omega

theorem noDelta5In_of_overgroups {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X) {t₂ : ℕ}
    (ht₂ : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → Nat.card T = t₂)
    (hover : ∀ T Y : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Y → Y = ⊤ ∨
      (Nat.card Y = 15 * t₂ → ∃ q : ℕ, q * 64 < t₂ ∧ ∀ (N : Subgroup ↥Y) [N.Normal],
        IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ q)) :
    NoDelta5In X :=
  fun _ hT _ _ hne hTB => not_isDelta5_of_overgroups hX ht₂ hover hT hne hTB

end CFSG.QuasithinUnique.A5.G3
