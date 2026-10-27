module

public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Abelb

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

variable {Y X : Type} [Group Y] [Group X]

theorem l34abel_mem_sup_iff {Jb D : Subgroup Y} {π : Y →* X} (hker : π.ker = D) {b : Y} :
    b ∈ Jb ⊔ D ↔ π b ∈ Jb.map π := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, hker]

theorem l34abel_exists_mul {Jb D : Subgroup Y} [D.Normal] {b : Y} (hb : b ∈ Jb ⊔ D) :
    ∃ j ∈ Jb, ∃ d ∈ D, j * d = b := by
  have hb' : b ∈ ((Jb ⊔ D : Subgroup Y) : Set Y) := hb
  rw [Subgroup.mul_normal Jb D] at hb'
  exact Set.mem_mul.mp hb'

theorem l34abel_comm_of_mem_sup {Jb D : Subgroup Y} {π : Y →* X} (hker : π.ker = D)
    (hDJ : ∀ d ∈ D, ∀ j ∈ Jb, d * j = j * d) (hDc : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d)
    (hJD : Jb ⊓ D = ⊥) {a b : Y} (ha : a ∈ Jb ⊔ D) (hb : b ∈ Jb ⊔ D)
    (hab : π a * π b = π b * π a) : a * b = b * a := by
  have hDn : D.Normal := hker ▸ π.normal_ker
  have hπD : ∀ d ∈ D, π d = 1 := fun d hd => by rw [← MonoidHom.mem_ker, hker]; exact hd
  obtain ⟨j₁, hj₁, d₁, hd₁, rfl⟩ := l34abel_exists_mul ha
  obtain ⟨j₂, hj₂, d₂, hd₂, rfl⟩ := l34abel_exists_mul hb
  rw [map_mul, map_mul, hπD d₁ hd₁, hπD d₂ hd₂, mul_one, mul_one] at hab
  have hc : j₁ * j₂ * j₁⁻¹ * j₂⁻¹ ∈ Jb ⊓ D := by
    refine Subgroup.mem_inf.mpr
      ⟨Jb.mul_mem (Jb.mul_mem (Jb.mul_mem hj₁ hj₂) (Jb.inv_mem hj₁)) (Jb.inv_mem hj₂), ?_⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group
  rw [hJD, Subgroup.mem_bot] at hc
  have hj : j₁ * j₂ = j₂ * j₁ := by
    calc j₁ * j₂ = (j₁ * j₂ * j₁⁻¹ * j₂⁻¹) * (j₂ * j₁) := by group
      _ = j₂ * j₁ := by rw [hc, one_mul]
  calc j₁ * d₁ * (j₂ * d₂) = j₁ * (d₁ * j₂) * d₂ := by group
    _ = j₁ * j₂ * (d₁ * d₂) := by rw [hDJ d₁ hd₁ j₂ hj₂]; group
    _ = j₂ * j₁ * (d₂ * d₁) := by rw [hj, hDc d₁ hd₁ d₂ hd₂]
    _ = j₂ * (j₁ * d₂) * d₁ := by group
    _ = j₂ * d₂ * (j₁ * d₁) := by rw [← hDJ d₂ hd₂ j₁ hj₁]; group

theorem l34abel_le_zpowers [Finite Y] {D : Subgroup Y} [D.Normal] (hDc : IsCyclic D)
    (hD3 : IsPGroup 3 D) {q : Y} (hq3 : ∃ n : ℕ, q ^ 3 ^ n = 1) (hqD : q ∉ D)
    (hΩ : ∀ b ∈ D ⊔ zpowers q, b ^ 3 = 1 → b ∈ D) : D ≤ zpowers q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_orderOf_eq_prime_pow_iff.mpr hq3
  have hq : IsPGroup 3 (zpowers q) := IsPGroup.of_card (n := c) (by rw [Nat.card_zpowers, hc])
  have hB3 : IsPGroup 3 (D ⊔ zpowers q : Subgroup Y) := IsPGroup.to_sup_of_normal_left hD3 hq
  have hBc : IsCyclic (D ⊔ zpowers q : Subgroup Y) := by
    by_contra hnc
    have h2 := two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hB3 hnc
    obtain ⟨E, hEB, hE, hEc⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three (D ⊔ zpowers q)
    have hED : E ≤ D := fun e he => hΩ e (hEB he) (hE.2 e he)
    have : IsCyclic E := Subgroup.isCyclic_of_le hED
    obtain ⟨e, he⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
    have h3 : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hE.2 e e.2))
    rw [he, hEc] at h3
    have h4 := Nat.le_of_dvd (by norm_num) h3
    have h5 : 3 ^ 2 ≤ 3 ^ CFSG.Open.pRank 3 (D ⊔ zpowers q) := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hDB : D ≤ D ⊔ zpowers q := le_sup_left
  have hqB : zpowers q ≤ D ⊔ zpowers q := le_sup_right
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hD3
  have hcD : Nat.card (D.subgroupOf (D ⊔ zpowers q)) = 3 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv, ha]
  have hcq : Nat.card ((zpowers q).subgroupOf (D ⊔ zpowers q)) = 3 ^ c := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hqB).toEquiv, Nat.card_zpowers, hc]
  rcases le_total a c with hac | hca
  · have hle : D.subgroupOf (D ⊔ zpowers q) ≤ (zpowers q).subgroupOf (D ⊔ zpowers q) :=
      IsCyclic.subgroup_le_iff_card_dvd.mpr (by rw [hcD, hcq]; exact Nat.pow_dvd_pow 3 hac)
    intro d hd
    exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_subgroupOf.mpr (show
      ((⟨d, hDB hd⟩ : ↥(D ⊔ zpowers q)) : Y) ∈ D from hd)))
  · exfalso
    have hle : (zpowers q).subgroupOf (D ⊔ zpowers q) ≤ D.subgroupOf (D ⊔ zpowers q) :=
      IsCyclic.subgroup_le_iff_card_dvd.mpr (by rw [hcD, hcq]; exact Nat.pow_dvd_pow 3 hca)
    exact hqD (Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_subgroupOf.mpr (show
      ((⟨q, hqB (mem_zpowers q)⟩ : ↥(D ⊔ zpowers q)) : Y) ∈ zpowers q from mem_zpowers q))))

theorem l34abel_le_sup_zpowers [Finite X] {A L : Subgroup X} (hA : IsPGroup 3 A) (hLA : L ≤ A)
    (hcard : Nat.card A ≤ 3 * Nat.card L) {g : X} (hgA : g ∈ A) (hgL : g ∉ L) :
    A ≤ L ⊔ zpowers g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL'A : L ⊔ zpowers g ≤ A := sup_le hLA (zpowers_le.mpr hgA)
  have hlt : L < L ⊔ zpowers g := lt_of_le_of_ne le_sup_left fun h =>
    hgL (by rw [h]; exact mem_sup_right (mem_zpowers g))
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hA.to_le hLA)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hA.to_le hL'A)
  have hcl := Subgroup.card_lt_of_lt hlt
  rw [ha, hb] at hcl
  have hab : a < b := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hcl
  have hge : Nat.card A ≤ Nat.card (L ⊔ zpowers g : Subgroup X) := by
    rw [hb]
    calc Nat.card A ≤ 3 * 3 ^ a := by rw [← ha]; exact hcard
      _ = 3 ^ (a + 1) := by ring
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hab
  exact (Subgroup.eq_of_le_of_card_ge hL'A hge).ge

theorem l34abel_comm [Finite Y] [Finite X] {Jb D : Subgroup Y} (π : Y →* X) (hker : π.ker = D)
    (hKn : (Jb.map π).Normal) (hDJ : ∀ d ∈ D, ∀ j ∈ Jb, d * j = j * d) (hDc : IsCyclic D)
    (hD3 : IsPGroup 3 D) (hJD : Jb ⊓ D = ⊥)
    (hK1 : ∀ A : Subgroup X, IsPGroup 3 A → A ≤ Jb.map π → ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hK6 : ∀ A : Subgroup X, IsPGroup 3 A →
      Nat.card A ≤ 3 * Nat.card (A ⊓ Jb.map π : Subgroup X))
    (hK9 : ∀ g : X, (∃ n : ℕ, g ^ 3 ^ n = 1) → g ^ 3 = 1)
    (hΩ : ∀ b : Y, b ^ 3 = 1 → b ∈ Jb ⊔ D) {Fb : Subgroup Y} (hF : IsPGroup 3 Fb)
    (hcen : ∀ a ∈ Fb, a ∈ Jb → ∀ b ∈ Fb, a * b = b * a) :
    ∀ a ∈ Fb, ∀ b ∈ Fb, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDn : D.Normal := hker ▸ π.normal_ker
  have hDab : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d := fun d hd e he =>
    congrArg Subtype.val ((IsCyclic.commGroup (α := D)).mul_comm ⟨d, hd⟩ ⟨e, he⟩)
  have hπD : ∀ d ∈ D, π d = 1 := fun d hd => by rw [← MonoidHom.mem_ker, hker]; exact hd
  have hFπ : IsPGroup 3 (Fb.map π) := hF.map π
  by_cases hFK : Fb ≤ Jb ⊔ D
  · intro a ha b hb
    have hmapK : Fb.map π ≤ Jb.map π := by
      rintro _ ⟨f, hf, rfl⟩
      exact (l34abel_mem_sup_iff hker).mp (hFK hf)
    exact l34abel_comm_of_mem_sup hker hDJ hDab hJD (hFK ha) (hFK hb)
      (hK1 _ hFπ hmapK _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩)
  obtain ⟨q, hqF, hqJD⟩ := IsConcreteLE.not_le_iff_exists.mp hFK
  have hq3 : ∃ n : ℕ, q ^ 3 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hF ⟨q, hqF⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hπq3 : π q ^ 3 = 1 := hK9 _ (by
    obtain ⟨n, hn⟩ := hq3
    exact ⟨n, by rw [← map_pow, hn, map_one]⟩)
  have hπqK : π q ∉ Jb.map π := fun h => hqJD ((l34abel_mem_sup_iff hker).mpr h)
  have hpow : ∀ k : ℤ, π q ^ k ∈ Jb.map π → π q ^ k = 1 := by
    intro k hk
    rcases l34abel_mem_zpowers_three hπq3 (zpow_mem (mem_zpowers (π q)) k) with h | h | h
    · exact h
    · rw [h] at hk
      exact absurd hk hπqK
    · rw [h, inv_mem_iff] at hk
      exact absurd hk hπqK
  have hqD : q ∉ D := fun h => hqJD (mem_sup_right h)
  have hBΩ : ∀ b ∈ D ⊔ zpowers q, b ^ 3 = 1 → b ∈ D := by
    intro b hb hb3
    have hb' : b ∈ ((D ⊔ zpowers q : Subgroup Y) : Set Y) := hb
    rw [Subgroup.normal_mul D (zpowers q)] at hb'
    obtain ⟨d, hd, z, hz, rfl⟩ := Set.mem_mul.mp hb'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have h1 : π q ^ k ∈ Jb.map π := by
      have h0 := (l34abel_mem_sup_iff hker).mp (hΩ _ hb3)
      rwa [map_mul, hπD d hd, one_mul, map_zpow] at h0
    have h2 : q ^ k ∈ D := by
      rw [← hker, MonoidHom.mem_ker, map_zpow]
      exact hpow k h1
    exact D.mul_mem hd h2
  have hDq : D ≤ zpowers q := l34abel_le_zpowers hDc hD3 hq3 hqD hBΩ
  have hDF : D ≤ Fb := hDq.trans (zpowers_le.mpr hqF)
  have hdec : ∀ f ∈ Fb, ∃ j ∈ Fb, j ∈ Jb ∧ ∃ z ∈ zpowers q, f = j * z := by
    intro f hf
    have hqA : π q ∈ Fb.map π := ⟨q, hqF, rfl⟩
    have hAle := l34abel_le_sup_zpowers hFπ inf_le_left (hK6 _ hFπ) hqA fun h => hπqK h.2
    have hnorm : zpowers (π q) ≤ normalizer ((Fb.map π ⊓ Jb.map π : Subgroup X) : Set X) := by
      rw [zpowers_le]
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hqA, ?_⟩
      rw [normalizer_eq_top_iff.mpr hKn]
      exact mem_top _
    have hmem : π f ∈ ((Fb.map π ⊓ Jb.map π ⊔ zpowers (π q) : Subgroup X) : Set X) :=
      hAle ⟨f, hf, rfl⟩
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hmem
    obtain ⟨l, hl, w, hw, hlw⟩ := Set.mem_mul.mp hmem
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    have hn : f * q ^ (-k) ∈ Jb ⊔ D := by
      rw [l34abel_mem_sup_iff hker, map_mul, map_zpow, ← hlw, zpow_neg, mul_inv_cancel_right]
      exact hl.2
    obtain ⟨j, hj, d, hd, hjd⟩ := l34abel_exists_mul hn
    have hjF : j ∈ Fb := by
      have e : j = f * q ^ (-k) * d⁻¹ := by rw [← hjd]; group
      rw [e]
      exact Fb.mul_mem (Fb.mul_mem hf (Fb.zpow_mem hqF _)) (Fb.inv_mem (hDF hd))
    refine ⟨j, hjF, hj, d * q ^ k, (zpowers q).mul_mem (hDq hd) (zpow_mem (mem_zpowers q) k), ?_⟩
    calc f = f * q ^ (-k) * q ^ k := by group
      _ = j * (d * q ^ k) := by rw [← hjd]; group
  intro a ha b hb
  obtain ⟨j₁, hj₁F, hj₁J, z₁, hz₁, rfl⟩ := hdec a ha
  obtain ⟨j₂, hj₂F, hj₂J, z₂, hz₂, rfl⟩ := hdec b hb
  have hz₁F : z₁ ∈ Fb := zpowers_le.mpr hqF hz₁
  have hz₂F : z₂ ∈ Fb := zpowers_le.mpr hqF hz₂
  have hzz : z₁ * z₂ = z₂ * z₁ := by
    obtain ⟨k₁, rfl⟩ := mem_zpowers_iff.mp hz₁
    obtain ⟨k₂, rfl⟩ := mem_zpowers_iff.mp hz₂
    rw [← zpow_add, ← zpow_add, add_comm]
  have e1 := hcen j₁ hj₁F hj₁J j₂ hj₂F
  have e2 := hcen j₂ hj₂F hj₂J z₁ hz₁F
  have e3 := hcen j₁ hj₁F hj₁J z₂ hz₂F
  calc j₁ * z₁ * (j₂ * z₂) = j₁ * (z₁ * j₂) * z₂ := by group
    _ = j₁ * j₂ * (z₁ * z₂) := by rw [← e2]; group
    _ = j₂ * j₁ * (z₂ * z₁) := by rw [e1, hzz]
    _ = j₂ * (j₁ * z₂) * z₁ := by group
    _ = j₂ * z₂ * (j₁ * z₁) := by rw [e3]; group

end CFSG.LocalAnalysis.RankThreeTheoremC
