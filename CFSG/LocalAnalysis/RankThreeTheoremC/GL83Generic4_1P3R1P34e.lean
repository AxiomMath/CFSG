module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34c

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem p34_exists_K₀ (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G}
    {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x)
    {J : Subgroup G} (hJ : IsM11Normal M x J) :
    ∃ K₀ : Subgroup G, K₀ ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) ∧
      IsElemAbelian 3 K₀ ∧ Nat.card K₀ = 3 ^ 2 ∧ x ∉ K₀ ∧
      ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 → ∃ n ∈ centralizer ({x} : Set G),
        n ∈ normalizer (K₀ : Set G) ∧ n * a * n⁻¹ = b := by
  have hY := p34_yData hS hU0 hKM hKA hp hM hgen hJ
  obtain ⟨Sbar, hSbar, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  set Q' : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQ'
  have hQ'p : IsPGroup 3 Q' := (P.isPGroup'.to_le inf_le_left).comap_subtype
  set L : Subgroup (C ⧸ O) := r1sBar x J with hL
  set SL : Subgroup (C ⧸ O) := (Sbar : Subgroup (C ⧸ O)) ⊓ L with hSL
  obtain ⟨hSLe, hSLc⟩ := hY.inf_elemAbelian hKM hKA Sbar
  set K' : Subgroup C := SL.comap π ⊓ Q' with hK'
  have hSLle : SL ≤ Q'.map π := inf_le_left.trans hSbar.le
  have hKmap : K'.map π = SL := CFSG.AGLEmbedding.map_comap_inf_eq π hSLle
  have hK'Q : K' ≤ Q' := inf_le_right
  have hK'p : IsPGroup 3 K' := hQ'p.to_le hK'Q
  have hK'card : Nat.card K' = 3 ^ 2 := by
    rw [← CFSG.AGLEmbedding.card_map_mk_of_isPGroup Nat.prime_three O hOcop hK'p]
    exact hKmap ▸ hSLc
  have hπK : ∀ a ∈ K', π a ∈ SL := fun a ha => hKmap ▸ Subgroup.mem_map_of_mem _ ha
  have hK'el : IsElemAbelian 3 K' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      change (a : C) * b = b * a
      refine p34_mk_inj hOcop hQ'p (Q'.mul_mem (hK'Q a.2) (hK'Q b.2))
        (Q'.mul_mem (hK'Q b.2) (hK'Q a.2)) ?_
      rw [map_mul, map_mul]
      exact p34_comm_of_isMulCommutative hSLe.1 (hπK a a.2) (hπK b b.2)
    · refine p34_mk_inj hOcop hQ'p (Q'.pow_mem (hK'Q ha) 3) Q'.one_mem ?_
      rw [map_pow, map_one]
      exact hSLe.2 _ (hπK a ha)
  refine ⟨K'.map C.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · calc K'.map C.subtype ≤ Q'.map C.subtype := Subgroup.map_mono hK'Q
      _ = (P : Subgroup G) ⊓ C := Subgroup.map_subgroupOf_eq_of_le inf_le_right
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hK'el C.subtype
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hK'card
  · rintro ⟨k, hk, hkx⟩
    have hkx' : k = ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ := Subtype.ext hkx
    have hz : π k ∈ center (C ⧸ O) := by rw [hkx']; exact hsh.mem_center
    have h1 : π k ∈ L ⊓ center (C ⧸ O) := ⟨(hπK k hk).2, hz⟩
    rw [hY.inf_center_eq_bot, Subgroup.mem_bot] at h1
    have h2 := hsh.orderOf_eq
    rw [← hkx', h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · intro a ha b hb ha1 hb1
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hπa1 : π a' ≠ 1 := fun h => ha1 (by
      have : a' = 1 := p34_mk_inj hOcop hQ'p (hK'Q ha') Q'.one_mem (by rw [h, map_one])
      rw [this]; rfl)
    have hπb1 : π b' ≠ 1 := fun h => hb1 (by
      have : b' = 1 := p34_mk_inj hOcop hQ'p (hK'Q hb') Q'.one_mem (by rw [h, map_one])
      rw [this]; rfl)
    obtain ⟨nb, -, hnbN, hnb⟩ := hY.sylow_transitive hKT Sbar (hπK a' ha') (hπK b' hb') hπa1 hπb1
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O nb
    have hn : n ∈ (normalizer ((K'.map π : Subgroup (C ⧸ O)) : Set (C ⧸ O))).comap π := by
      rw [Subgroup.mem_comap, hKmap]
      exact hnbN
    have hfr := CFSG.AGLEmbedding.comap_normalizer_map_le_sup Nat.prime_three O hOcop hK'p hn
    have hfr' : n ∈ ((O ⊔ normalizer (K' : Set C) : Subgroup C) : Set C) := hfr
    rw [Subgroup.normal_mul] at hfr'
    obtain ⟨o, ho, n₁, hn₁, hon⟩ := hfr'
    have hon' : o * n₁ = n := hon
    have ho' : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    have hπn : π n = π n₁ := by rw [← hon', map_mul, ho', one_mul]
    have hmem : n₁ * a' * n₁⁻¹ ∈ K' := (mem_normalizer_iff.mp hn₁ a').mp ha'
    have heq : n₁ * a' * n₁⁻¹ = b' := by
      refine p34_mk_inj hOcop hQ'p (hK'Q hmem) (hK'Q hb') ?_
      rw [map_mul, map_mul, map_inv, ← hπn]
      exact hnb
    refine ⟨(n₁ : G), n₁.2, ?_, congrArg Subtype.val heq⟩
    exact Subgroup.le_normalizer_map C.subtype ⟨n₁, hn₁, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
