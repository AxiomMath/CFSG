module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallWeak

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

section Quotient

variable {N : Subgroup G} [N.Normal]

omit [Finite G] in
theorem card_map_mk_mul (hN2 : Nat.card N = 2) {K : Subgroup G} (hNK : N ≤ K) :
    Nat.card (K.map (QuotientGroup.mk' N)) * 2 = Nat.card K := by
  set f := (QuotientGroup.mk' N).comp K.subtype with hf
  have hker : f.ker = N.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf, hf, MonoidHom.comp_apply, coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hrange : f.range = K.map (QuotientGroup.mk' N) := by
    rw [hf, MonoidHom.range_comp, range_subtype]
  have h := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
    Nat.card_congr (subgroupOfEquivOfLe hNK).toEquiv, hN2] at h
  exact h.symm

omit [Finite G] in
theorem card_comap_mk (hN2 : Nat.card N = 2) (K : Subgroup (G ⧸ N)) :
    Nat.card (K.comap (QuotientGroup.mk' N)) = 2 * Nat.card K := by
  have hle : N ≤ K.comap (QuotientGroup.mk' N) := fun n hn => by
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem K
  have h := card_map_mk_mul hN2 hle
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] at h
  omega

theorem weak_of_quotient (hN2 : Nat.card N = 2) (hND : N ≤ D)
    (hW : HallWeakConclusion (D.map (QuotientGroup.mk' N))) : HallWeakConclusion D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hDmem : ∀ y : G, π y ∈ D.map π → y ∈ D := fun y hy => by
    rw [← comap_map_eq_self (show π.ker ≤ D by rw [hker]; exact hND)]
    exact hy
  obtain ⟨S, T, hT, hDS, hST, hsc, hinv, hcard⟩ := hW
  refine ⟨S.comap π, T.comap π, ?_, fun d hd => hDS ⟨d, hd, rfl⟩, comap_mono hST, ?_, ?_, ?_⟩
  · rw [isSylowOf_iff] at hT ⊢
    obtain ⟨-, hT2, hTi⟩ := hT
    refine ⟨le_top, hT2.comap_of_ker_isPGroup π ?_, ?_⟩
    · rw [hker]
      exact IsPGroup.of_card (n := 1) (by rw [hN2]; norm_num)
    · rw [relIndex_top_right] at hTi ⊢
      rwa [index_comap_of_surjective _ hπs]
  · intro s hs g hg
    have h := hsc (π s) hs (π g) (by simpa using hg)
    change π (g⁻¹ * s * g) ∈ S
    simpa using h
  · intro s hs hs2
    exact hDmem s (hinv (π s) hs (by rw [← map_mul, hs2, map_one]))
  · have h1 := card_comap_mk hN2 S
    have h2 := card_map_mk_mul hN2 hND
    rw [← hπ] at h1 h2
    rw [h1]
    omega

end Quotient

omit [Finite G] in
theorem zpowers_cz_normal (hzc : ∀ g : G, g * cz c = cz c * g) : (zpowers (cz c)).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have hc : Commute g (cz c ^ k) := Commute.zpow_right (hzc g) k
    rw [hc.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) k⟩

theorem mem_zpowers_cz_iff (hk : 4 ∣ orderOf c) {x : G} :
    x ∈ zpowers (cz c) ↔ x = 1 ∨ x = cz c := by
  constructor
  · rintro ⟨i, rfl⟩
    have h := zpow_mod_orderOf (cz c) i
    rw [orderOf_cz hk] at h
    rcases Int.emod_two_eq_zero_or_one i with hi | hi
    · left
      change cz c ^ i = 1
      rw [← h, show ((2 : ℕ) : ℤ) = 2 from rfl, hi, zpow_zero]
    · right
      change cz c ^ i = cz c
      rw [← h, show ((2 : ℕ) : ℤ) = 2 from rfl, hi, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem card_zpowers_cz (hk : 4 ∣ orderOf c) : Nat.card (zpowers (cz c)) = 2 := by
  rw [Nat.card_zpowers, orderOf_cz hk]

variable [(zpowers (cz c)).Normal]

theorem orderOf_mk_c (hk : 4 ∣ orderOf c) :
    orderOf (QuotientGroup.mk' (zpowers (cz c)) c) = orderOf c / 2 := by
  set π := QuotientGroup.mk' (zpowers (cz c))
  have hker : ∀ y : G, π y = 1 ↔ y ∈ zpowers (cz c) := fun y => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hker]
    exact mem_zpowers _
  · have h1 : π (c ^ orderOf (π c)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
    rw [hker] at h1
    have h2 : (c ^ orderOf (π c)) ^ 2 = 1 := by
      rcases (mem_zpowers_cz_iff hk).mp h1 with h | h
      · rw [h, one_pow]
      · rw [h, sq, cz_mul_cz hk]
    rw [← pow_mul] at h2
    obtain ⟨t, ht⟩ := orderOf_dvd_of_pow_eq_one h2
    obtain ⟨h, hh⟩ : ∃ h, orderOf c = 2 * h := ⟨orderOf c / 2, by omega⟩
    refine ⟨t, ?_⟩
    rw [show orderOf c / 2 = h by omega]
    rw [hh] at ht
    have h4 : orderOf (π c) * 2 = (h * t) * 2 := by rw [ht]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h4

omit [Finite G] in
theorem data_map (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹)) :
    ∀ x ∈ D.map (QuotientGroup.mk' (zpowers (cz c))),
      x ∈ zpowers (QuotientGroup.mk' (zpowers (cz c)) c) ∨
        (x * x = 1 ∧ x * QuotientGroup.mk' (zpowers (cz c)) c * x⁻¹ =
          (QuotientGroup.mk' (zpowers (cz c)) c)⁻¹) := by
  rintro _ ⟨x, hx, rfl⟩
  rcases hD x hx with h | ⟨h1, h2⟩
  · left
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp h
    rw [map_zpow]
    exact zpow_mem (mem_zpowers _) i
  · right
    refine ⟨by rw [← map_mul, h1, map_one], ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul, h2, map_inv]

theorem card_map_D (hk : 4 ∣ orderOf c) (hcard : Nat.card D = 2 * orderOf c) (hcD : c ∈ D) :
    Nat.card (D.map (QuotientGroup.mk' (zpowers (cz c)))) =
      2 * orderOf (QuotientGroup.mk' (zpowers (cz c)) c) := by
  have h := card_map_mk_mul (card_zpowers_cz hk) (zpowers_le.mpr (cz_mem hcD))
  rw [orderOf_mk_c hk]
  omega

theorem exists_bad_of_not_sic (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹))
    (hk : 4 ∣ orderOf c) (hcD : c ∈ D)
    (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)
    (hnot : ¬ ∀ x ∈ normalizer ((D.map (QuotientGroup.mk' (zpowers (cz c))) : Subgroup _) :
        Set (G ⧸ zpowers (cz c))), x ∉ D.map (QuotientGroup.mk' (zpowers (cz c))) →
      orderOf x = 2 → ∀ d ∈ D.map (QuotientGroup.mk' (zpowers (cz c))), orderOf d = 2 →
        ∀ g : G ⧸ zpowers (cz c), g⁻¹ * x * g ≠ d) :
    ∃ x ∈ normalizer (D : Set G), x ∉ D ∧ ∃ d ∈ D, d * d = cz c ∧ ∃ g : G, g⁻¹ * x * g = d := by
  set π := QuotientGroup.mk' (zpowers (cz c)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ y : G, π y = 1 ↔ y ∈ zpowers (cz c) := fun y => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  have hND : zpowers (cz c) ≤ D := zpowers_le.mpr (cz_mem hcD)
  have hDmem : ∀ y : G, y ∈ D ↔ π y ∈ D.map π := fun y => by
    constructor
    · exact fun hy => ⟨y, hy, rfl⟩
    · intro hy
      rw [← comap_map_eq_self (show π.ker ≤ D by rw [QuotientGroup.ker_mk']; exact hND)]
      exact hy
  push Not at hnot
  obtain ⟨x', hxN, hxD, hx2, d', hdD', hd2, g', hg'⟩ := hnot
  obtain ⟨x, rfl⟩ := hπs x'
  obtain ⟨g, rfl⟩ := hπs g'
  obtain ⟨d₀, hd₀, rfl⟩ := hdD'
  have hxN' : x ∈ normalizer (D : Set G) := by
    rw [mem_normalizer_iff] at hxN ⊢
    intro y
    rw [hDmem y, hDmem (x * y * x⁻¹), hxN (π y), map_mul, map_mul, map_inv]
  have hxD' : x ∉ D := fun h => hxD ((hDmem x).mp h)
  set d := g⁻¹ * x * g with hd
  have hπd : π d = π d₀ := by rw [hd, map_mul, map_mul, map_inv, hg']
  have hdD : d ∈ D := by
    have h : d₀⁻¹ * d ∈ zpowers (cz c) := by
      rw [← hker, map_mul, map_inv, hπd, inv_mul_cancel]
    have : d = d₀ * (d₀⁻¹ * d) := by group
    rw [this]
    exact mul_mem hd₀ (hND h)
  rw [← hπd] at hd2
  have hdN : d ∉ zpowers (cz c) := fun h => by
    rw [← hker] at h
    rw [h, orderOf_one] at hd2
    omega
  have hdd : d * d ∈ zpowers (cz c) := by
    rw [← hker, map_mul, ← sq, ← hd2, pow_orderOf_eq_one]
  rcases hD d hdD with hdC | ⟨hd1, -⟩
  · refine ⟨x, hxN', hxD', d, hdD, ?_, g, rfl⟩
    rcases (mem_zpowers_cz_iff hk).mp hdd with h | h
    · exfalso
      rcases eq_one_or_eq_cz hk hdC h with h' | h'
      · exact hdN (by rw [h']; exact one_mem _)
      · exact hdN (by rw [h']; exact mem_zpowers _)
    · exact h
  · exfalso
    have hd1' : d ≠ 1 := fun h => hdN (by rw [h]; exact one_mem _)
    have hdo : orderOf d = 2 := orderOf_eq_prime (by rw [sq]; exact hd1) hd1'
    have hxd : x = g * d * g⁻¹ := by rw [hd]; group
    have hxo : orderOf x = 2 := by
      rw [hxd, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hdo]
    exact hcl x hxN' hxD' hxo d hdD hdo g rfl

end CFSG.ComponentClassification.Foote5.HallGen
