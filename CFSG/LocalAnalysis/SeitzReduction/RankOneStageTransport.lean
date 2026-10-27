module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStage

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section MapEquiv

variable {D E : Type*} [Group D] [Group E] (e : D ≃* E)

theorem map_equiv_centralizer_eq (H : Subgroup D) :
    (centralizer (H : Set D)).map e.toMonoidHom =
      centralizer ((H.map e.toMonoidHom : Subgroup E) : Set E) := by
  ext x
  rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hy
    have h1 := congrArg e (hx z hz)
    simpa using h1
  · intro hx z hz
    apply e.injective
    have h1 := hx (e z) (mem_map_of_mem e.toMonoidHom hz)
    simpa using h1

theorem map_equiv_inf (H K : Subgroup D) :
    (H ⊓ K).map e.toMonoidHom = H.map e.toMonoidHom ⊓ K.map e.toMonoidHom :=
  map_inf_eq H K e.toMonoidHom e.injective

theorem card_map_equiv (H : Subgroup D) : Nat.card (H.map e.toMonoidHom) = Nat.card H :=
  card_map_of_injective e.injective

theorem normal_subgroupOf_map_equiv {H K : Subgroup D} (hHK : H ≤ K)
    (h : (H.subgroupOf K).Normal) :
    ((H.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer hHK] at h
  rw [normal_subgroupOf_iff_le_normalizer (map_mono hHK), ← map_equiv_normalizer_eq]
  exact map_mono h

theorem exists_sylow_map_equiv [Finite D] {p : ℕ} [Fact p.Prime] {H K : Subgroup D}
    (hHK : H ≤ K) (h : ∃ T : Sylow p K, (T : Subgroup K) = H.subgroupOf K) :
    ∃ T : Sylow p (K.map e.toMonoidHom),
      (T : Subgroup _) = (H.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom) := by
  have : Finite E := Finite.of_equiv D e.toEquiv
  obtain ⟨T, hT⟩ := h
  have hS : ABGLocalTools.IsSylowOf p H K := ⟨T, by
    rw [hT, subgroupOf_map_subtype, inf_eq_left.mpr hHK]⟩
  rw [ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨-, hp, hdvd⟩ := hS
  have hS' : ABGLocalTools.IsSylowOf p (H.map e.toMonoidHom) (K.map e.toMonoidHom) := by
    rw [ABGLocalTools.isSylowOf_iff]
    exact ⟨map_mono hHK, hp.map _, by rwa [relIndex_map_map_of_injective _ _ e.injective]⟩
  exact hS'.exists_sylow_eq_subgroupOf

end MapEquiv

section Singer

variable {G : Type*} [Group G]

theorem gmsSinger_of_element [Finite G] {X U : Subgroup G} {d : G} (hUX : U ≤ X)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hdX : d ∈ X) (hdN : d ∈ normalizer (U : Set G))
    (hNX : X ⊓ normalizer (U : Set G) ≤ U ⊔ zpowers d)
    (htr : ∀ a ∈ U, ∀ b ∈ U, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, d ^ k * a * (d ^ k)⁻¹ = b)
    (hfix : ∀ k : ℕ, ∀ a ∈ U, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1)
    (hU1 : ∃ x ∈ U, x ≠ 1) :
    IsCyclic (GMSNormalizerQuotient X U) ∧ Nat.card (GMSNormalizerQuotient X U) = orderOf d ∧
      ∀ u v : U, u ≠ 1 → v ≠ 1 →
        ∃! c : GMSNormalizerQuotient X U, gmsQuotConjAct X U c u = v := by
  have hreg : ∀ x ∈ U, x ≠ 1 → ∀ y ∈ U, y ≠ 1 →
      ∃! c : zpowers d, (c : G) * x * (c : G)⁻¹ = y := by
    intro x hx hx1 y hy hy1
    obtain ⟨k, hk⟩ := htr x hx y hy hx1 hy1
    refine ⟨⟨d ^ k, pow_mem (mem_zpowers d) k⟩, hk, ?_⟩
    rintro ⟨c, hc⟩ hc'
    have hc'' : c * x * c⁻¹ = y := hc'
    obtain ⟨m, hm⟩ : ∃ m : ℕ, d ^ m = (d ^ k)⁻¹ * c :=
      (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2
        (mul_mem (inv_mem (pow_mem (mem_zpowers d) k)) hc))
    have hfx : d ^ m * x * (d ^ m)⁻¹ = x := by
      rw [hm]
      calc (d ^ k)⁻¹ * c * x * ((d ^ k)⁻¹ * c)⁻¹ = (d ^ k)⁻¹ * (c * x * c⁻¹) * d ^ k := by group
        _ = (d ^ k)⁻¹ * (d ^ k * x * (d ^ k)⁻¹) * d ^ k := by rw [hc'', hk]
        _ = x := by group
    have hm1 : d ^ m = 1 := hfix m x hx hx1 hfx
    apply Subtype.ext
    show c = d ^ k
    rw [hm1] at hm
    calc c = d ^ k * ((d ^ k)⁻¹ * c) := by group
      _ = d ^ k := by rw [← hm, mul_one]
  obtain ⟨hcyc, hcard, hreg'⟩ := gmsNormalizerQuotient_of_regular_complement hUX hUab
    (zpowers_le.mpr hdX) (zpowers_le.mpr hdN) hNX inferInstance hreg hU1
  exact ⟨hcyc, by rw [hcard, Nat.card_zpowers], hreg'⟩

end Singer

section Stage

variable {D E : Type*} [Group D] [Group E] [Finite D] {R X U P : Subgroup D} {n : ℕ}

theorem SmallRootStage.map_mulEquiv (e : D ≃* E) (h : SmallRootStage R X U P n) :
    SmallRootStage (R.map e.toMonoidHom) (X.map e.toMonoidHom) (U.map e.toMonoidHom)
      (P.map e.toMonoidHom) n := by
  have : Finite E := Finite.of_equiv D e.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, -, ⟨hRel, -, -⟩, ⟨hXN, hXn, hXC⟩, ⟨hUel, hUX, hUsyl, hUcard⟩, -,
    ⟨hPN, hPsyl, hUP, hRP, hPU, hUR, hPC, hVn⟩⟩ := h.1
  obtain ⟨d, hdNX, hdord, hNXeq, hdtr, hdfix⟩ := h.exists_singer
  have hR' : Nat.card (R.map e.toMonoidHom) = 2 := by
    rw [card_map_equiv, h.card_eq_two]
  have hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hdX : d ∈ X := (mem_inf.mp hdNX).1
  have hdN : d ∈ normalizer (U : Set D) := (mem_inf.mp hdNX).2
  have hconj : ∀ (k : ℕ) (a : D), e d ^ k * e a * (e d ^ k)⁻¹ = e (d ^ k * a * (d ^ k)⁻¹) := by
    intro k a
    simp [map_pow]
  have hsinger := gmsSinger_of_element (X := X.map e.toMonoidHom) (U := U.map e.toMonoidHom)
    (d := e d) (map_mono hUX)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      change e x * e y = e y * e x
      rw [← map_mul, ← map_mul, hUab x hx y hy])
    (mem_map_of_mem _ hdX)
    (by rw [← map_equiv_normalizer_eq]; exact mem_map_of_mem _ hdN)
    (by
      rw [← map_equiv_normalizer_eq, ← map_equiv_inf, hNXeq, Subgroup.map_sup,
        MonoidHom.map_zpowers]
      rfl)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ha1 hb1
      have ha1' : a ≠ 1 := fun h1 => ha1 (by rw [h1, map_one])
      have hb1' : b ≠ 1 := fun h1 => hb1 (by rw [h1, map_one])
      obtain ⟨k, hk⟩ := hdtr a ha b hb ha1' hb1'
      refine ⟨k, ?_⟩
      change e d ^ k * e a * (e d ^ k)⁻¹ = e b
      rw [hconj, hk])
    (by
      rintro k _ ⟨a, ha, rfl⟩ ha1 hk
      have ha1' : a ≠ 1 := fun h1 => ha1 (by rw [h1, map_one])
      change e d ^ k * e a * (e d ^ k)⁻¹ = e a at hk
      rw [hconj] at hk
      have h1 := hdfix k a ha ha1' (e.injective hk)
      rw [← map_pow, h1, map_one])
    (by
      have h8 : 1 < Nat.card (U.map e.toMonoidHom) := by
        rw [card_map_equiv, hUcard]
        exact Nat.one_lt_two_pow (by omega)
      have : Nontrivial (U.map e.toMonoidHom) := Finite.one_lt_card_iff_nontrivial.mp h8
      obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : U.map e.toMonoidHom)
      exact ⟨x, hx, fun h1 => hx1 (Subtype.ext h1)⟩)
  obtain ⟨hcyc, hcard, hreg⟩ := hsinger
  have hXN' : X.map e.toMonoidHom ≤ normalizer ((R.map e.toMonoidHom : Subgroup E) : Set E) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono hXN
  have hPN' : P.map e.toMonoidHom ≤ normalizer ((R.map e.toMonoidHom : Subgroup E) : Set E) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono hPN
  refine ⟨⟨hn, ⟨by rw [hR']; exact even_two, fun g hg => by
      rw [card_inf_conj_eq_one_of_card_eq_two hR' hg]; exact odd_one⟩,
    ⟨IsElementaryAbelian.map (A := R) e.toMonoidHom, le_rfl, ?_⟩,
    ⟨hXN', ?_, ?_⟩,
    ⟨IsElementaryAbelian.map (A := U) e.toMonoidHom, map_mono hUX,
      exists_sylow_map_equiv e hUX hUsyl, by rw [card_map_equiv, hUcard]⟩,
    ⟨hcyc, by rw [hcard, MulEquiv.orderOf_eq, hdord], hreg⟩,
    ⟨hPN', ?_, map_mono hUP, map_mono hRP, ?_, ?_, ?_, ?_⟩⟩, hR', ?_⟩
  ·
    have hp : IsPGroup 2 (⊤ : Subgroup (R.map e.toMonoidHom)) :=
      IsPGroup.of_card (n := 1) (by rw [Subgroup.card_top, hR', pow_one])
    exact ⟨hp.toSylow (by rw [Subgroup.index_top]; norm_num),
      by rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_self]⟩
  ·
    have h1 := normal_subgroupOf_map_equiv e hXN hXn
    rwa [map_equiv_normalizer_eq] at h1
  · rw [← map_equiv_centralizer_eq]
    exact map_mono hXC
  ·
    have h1 := exists_sylow_map_equiv e hPN hPsyl
    rwa [map_equiv_normalizer_eq] at h1
  · rw [← map_equiv_normalizer_eq]
    exact map_mono hPU
  · rw [← map_equiv_inf, hUR, Subgroup.map_bot]
  · rw [← map_equiv_centralizer_eq, ← map_equiv_inf, hPC, Subgroup.map_sup]
  · rw [← Subgroup.map_sup]
    exact normal_subgroupOf_map_equiv e (sup_le hUP hRP) hVn
  · rw [← map_equiv_normalizer_eq, ← map_equiv_centralizer_eq, ← map_equiv_inf,
      h.normalizer_inf_centralizer, Subgroup.map_sup]

end Stage

end CFSG.SeitzReduction.RankOne
