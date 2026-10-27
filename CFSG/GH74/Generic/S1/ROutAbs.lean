module

public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GH74.Generic.OuterRank

public section

namespace CFSG.GH74.Generic.S1

open Subgroup CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Filter.ClassicalOdd

variable {C : Type} [Group C]

theorem rconjNormal_eq_one_iff {K : Subgroup C} [K.Normal] {c : C} :
    (MulAut.conjNormal c : MulAut K) = 1 ↔ ∀ k ∈ K, c * k = k * c := by
  constructor
  · intro h k hk
    have := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : C)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc c * k = c * k * c⁻¹ * c := by group
      _ = k * c := by rw [this]
  · intro h
    ext ⟨k, hk⟩
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [h k hk]; group

instance semidirect_finite {N G : Type} [Group N] [Group G] [Finite N] [Finite G]
    {φ : G →* MulAut N} : Finite (N ⋊[φ] G) :=
  Finite.of_equiv (N × G) SemidirectProduct.equivProd.symm

theorem exists_two_power_rep {G H : Type} [Group G] [Finite G] [Group H] (ρ : G →* H) (g : G)
    (n : ℕ) (hn : ρ g ^ (2 ^ n) = 1) :
    ∃ g' : G, (∃ m : ℕ, g' ^ (2 ^ m) = 1) ∧ ρ g' = ρ g := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · refine ⟨1, ⟨0, by simp⟩, ?_⟩
    rw [map_one]
    simpa using hn.symm
  have ho : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd ho
  have hcop : Nat.Coprime b (2 ^ n) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hb)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_two_pow hnpos.ne')
  refine ⟨g ^ (b * u), ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, show b * u * 2 ^ a = orderOf g * u by rw [hab]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · rw [map_pow]
    have h1 : b * u = 1 + 2 ^ n * (b * u / 2 ^ n) := by
      have := Nat.div_add_mod (b * u) (2 ^ n)
      rw [hu] at this
      omega
    rw [h1, pow_add, pow_mul, hn, one_pow, mul_one, pow_one]

theorem index_le_two_of_frame_type [Finite C] (hC : Gen4 C) (K : Subgroup C) [K.Normal]
    (hcent : centralizer (K : Set C) ≤ K)
    {𝔾 : Type} [Group 𝔾] [Finite 𝔾] (ρ : 𝔾 →* MulAut ↥K) {Y : Type} [Group Y] [Finite Y]
    (hYcomm : ∀ y y' : Y, y * y' = y' * y) (χ : 𝔾 →* Y)
    (hcover : ∀ t : C, (∃ n : ℕ, t ^ (2 ^ n) = 1) → ∃ g : 𝔾, ρ g = MulAut.conjNormal t)
    (hker : ∀ g : 𝔾, χ g = 1 → ∃ k : ↥K, ρ g = MulAut.conjNormal (k : C))
    (φ : Q8 × Q8 →* C) (hφ : Function.Injective φ) (hφK : ∀ a, φ a ∈ K)
    (g₀ : 𝔾) (hg₀ : ∃ n : ℕ, ρ g₀ ^ (2 ^ n) = 1)
    (hfix : ∀ a, ρ g₀ ⟨φ a, hφK a⟩ = ⟨φ a, hφK a⟩)
    (hninn : ∀ k : ↥K, ρ g₀ ≠ MulAut.conjNormal (k : C))
    (hZ : ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → ∃ n : ℕ, z ^ (2 ^ n) = 1)
    (hgrp : ∀ I : Subgroup Y, (∀ y ∈ I, ∃ n : ℕ, y ^ (2 ^ n) = 1) → χ g₀ ∉ I → Nat.card I ≤ 2)
    (T : Subgroup C) (hT : IsPGroup 2 T) : (K.subgroupOf T).index ≤ 2 := by
  classical
  let 𝕋 : Subgroup 𝔾 :=
    { carrier := {g | ∃ t ∈ T, ρ g = MulAut.conjNormal t}
      mul_mem' := by
        rintro _ _ ⟨t, ht, h⟩ ⟨t', ht', h'⟩
        exact ⟨t * t', T.mul_mem ht ht', by rw [map_mul, h, h', map_mul]⟩
      one_mem' := ⟨1, T.one_mem, by rw [map_one, map_one]⟩
      inv_mem' := by
        rintro _ ⟨t, ht, h⟩
        exact ⟨t⁻¹, T.inv_mem ht, by rw [map_inv, h, map_inv]⟩ }
  have hpow : ∀ t ∈ T, ∃ n : ℕ, t ^ (2 ^ n) = 1 := by
    intro t ht
    obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  let S₂ : Set Y := {y | ∃ g ∈ 𝕋, (∃ m : ℕ, g ^ (2 ^ m) = 1) ∧ χ g = y}
  let I : Subgroup Y := Subgroup.closure S₂
  have hIle : ∀ y ∈ I, y ∈ 𝕋.map χ := by
    intro y hy
    refine (Subgroup.closure_le (𝕋.map χ)).2 ?_ hy
    rintro _ ⟨g, hg, -, rfl⟩
    exact ⟨g, hg, rfl⟩
  have hI2 : ∀ y ∈ I, ∃ n : ℕ, y ^ (2 ^ n) = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, -, ⟨m, hm⟩, rfl⟩ := hx
      exact ⟨m, by rw [← map_pow, hm, map_one]⟩
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      have hc : Commute x y := hYcomm x y
      have h1 : x ^ (2 ^ (a + b)) = 1 := by rw [pow_add, pow_mul, ha, one_pow]
      have h2 : y ^ (2 ^ (a + b)) = 1 := by rw [add_comm, pow_add, pow_mul, hb, one_pow]
      rw [hc.mul_pow, h1, h2, one_mul]
    | inv x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [inv_pow, ha, inv_one]⟩
  have hy₀ : χ g₀ ∉ I := by
    intro hy₀I
    obtain ⟨g, ⟨t, ht, hgt⟩, hχ⟩ := hIle _ hy₀I
    have h1 : χ (g * g₀⁻¹) = 1 := by rw [map_mul, map_inv, hχ, mul_inv_cancel]
    obtain ⟨k₀, hk₀⟩ := hker _ h1
    have hu : ρ g₀ = MulAut.conjNormal ((k₀ : C)⁻¹ * t) := by
      have h3 : ρ g * (ρ g₀)⁻¹ = MulAut.conjNormal (k₀ : C) := by
        rw [← map_inv, ← map_mul]; exact hk₀
      rw [hgt] at h3
      rw [map_mul, map_inv]
      calc ρ g₀ = (MulAut.conjNormal t * (ρ g₀)⁻¹)⁻¹ * MulAut.conjNormal t := by group
        _ = _ := by rw [h3]
    set u : C := (k₀ : C)⁻¹ * t with hu_def
    obtain ⟨n, hn⟩ := hg₀
    have hun : (MulAut.conjNormal (u ^ (2 ^ n)) : MulAut K) = 1 := by
      rw [map_pow, ← hu, hn]
    have hcentu : ∀ k ∈ K, u ^ (2 ^ n) * k = k * u ^ (2 ^ n) := rconjNormal_eq_one_iff.1 hun
    have hinK : u ^ (2 ^ n) ∈ K := hcent (by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcentu k hk).symm)
    obtain ⟨n', hn'⟩ := hZ _ hinK hcentu
    have hun2 : u ^ (2 ^ (n + n')) = 1 := by
      rw [pow_add, pow_mul, hn']
    have hP : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_pow_two_pow_eq_one hun2
    have hcomm1 : ∀ a, Commute (φ a) u := by
      intro a
      have h4 := congrArg (fun m : K => (m : C)) (hfix a)
      simp only [hu, MulAut.conjNormal_apply] at h4
      show φ a * u = u * φ a
      calc φ a * u = (u * φ a * u⁻¹) * u := by rw [h4]
        _ = u * φ a := by group
    have hle := q8q8_commuting_two_subgroup_le hC φ hφ (Subgroup.zpowers u) hP
      (fun a t' ht' => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht'
        exact ((hcomm1 a).zpow_right m).eq)
    have huφ : u ∈ φ.range := hle (Subgroup.mem_zpowers u)
    have huK : u ∈ K := by
      obtain ⟨a, ha⟩ := huφ
      rw [← ha]; exact hφK a
    exact hninn ⟨u, huK⟩ hu
  have hcard : Nat.card I ≤ 2 := hgrp I hI2 hy₀
  have hdist : ∀ (s s' : T) (g g' : 𝔾), ρ g = MulAut.conjNormal (s : C) →
      ρ g' = MulAut.conjNormal (s' : C) → χ g = χ g' →
      (QuotientGroup.mk s : T ⧸ K.subgroupOf T) = QuotientGroup.mk s' := by
    intro s s' g g' hs hs' hχ
    have h1 : χ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, hχ, inv_mul_cancel]
    obtain ⟨k, hk⟩ := hker _ h1
    rw [map_mul, map_inv, hs, hs', ← map_inv, ← map_mul] at hk
    have h5 : (MulAut.conjNormal ((k : C)⁻¹ * ((s : C)⁻¹ * (s' : C))) : MulAut K) = 1 := by
      have := congrArg (fun φ : MulAut K => (MulAut.conjNormal (k : C))⁻¹ * φ) hk
      simp only [map_mul, map_inv] at this ⊢
      rw [← map_inv] at this
      simpa using this
    have h6 := rconjNormal_eq_one_iff.1 h5
    have h7 : (k : C)⁻¹ * ((s : C)⁻¹ * (s' : C)) ∈ K := hcent (by
      rw [Subgroup.mem_centralizer_iff]
      intro k' hk'
      exact (h6 k' hk').symm)
    have h8 : (s : C)⁻¹ * (s' : C) ∈ K := by
      have := K.mul_mem k.2 h7
      simpa using this
    rw [QuotientGroup.eq]
    exact (Subgroup.mem_subgroupOf).2 h8
  by_contra hlt
  push Not at hlt
  have := Fintype.ofFinite (T ⧸ K.subgroupOf T)
  have h3 : 2 < Fintype.card (T ⧸ K.subgroupOf T) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]; exact hlt
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h3
  obtain ⟨sa, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨sb, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨sc, rfl⟩ := QuotientGroup.mk_surjective c
  have hrep : ∀ s : T, ∃ g : 𝔾, g ∈ 𝕋 ∧ (∃ m : ℕ, g ^ (2 ^ m) = 1) ∧
      ρ g = MulAut.conjNormal (s : C) := by
    intro s
    obtain ⟨g, hg⟩ := hcover (s : C) (hpow _ s.2)
    obtain ⟨n, hn⟩ := hpow _ s.2
    have hn' : ρ g ^ (2 ^ n) = 1 := by
      rw [hg, ← map_pow, hn, map_one]
    obtain ⟨g', hg'2, hg'⟩ := exists_two_power_rep ρ g n hn'
    exact ⟨g', ⟨s, s.2, by rw [hg', hg]⟩, hg'2, by rw [hg', hg]⟩
  obtain ⟨ga, hgaT, hga2, hga⟩ := hrep sa
  obtain ⟨gb, hgbT, hgb2, hgb⟩ := hrep sb
  obtain ⟨gc, hgcT, hgc2, hgc⟩ := hrep sc
  have hmem : ∀ g : 𝔾, g ∈ 𝕋 → (∃ m : ℕ, g ^ (2 ^ m) = 1) → χ g ∈ I :=
    fun g hg hg2 => Subgroup.subset_closure ⟨g, hg, hg2, rfl⟩
  have hI3 : 2 < Nat.card I := by
    have : Fintype I := Fintype.ofFinite I
    rw [Nat.card_eq_fintype_card]
    refine Fintype.two_lt_card_iff.2 ⟨⟨χ ga, hmem ga hgaT hga2⟩, ⟨χ gb, hmem gb hgbT hgb2⟩,
      ⟨χ gc, hmem gc hgcT hgc2⟩, ?_, ?_, ?_⟩
    · intro h
      exact hab (hdist sa sb ga gb hga hgb (congrArg Subtype.val h))
    · intro h
      exact hac (hdist sa sc ga gc hga hgc (congrArg Subtype.val h))
    · intro h
      exact hbc (hdist sb sc gb gc hgb hgc (congrArg Subtype.val h))
  omega

end CFSG.GH74.Generic.S1
