module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111E16

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81NineSeventeenOne : Prop :=
  AGLGlobal G → ∀ (p : ℕ) (P : Sylow p G) (M H : Subgroup G), AGLMuAt p P M →
    GLBIsMaxTwoLocal H → ¬ H ≤ M →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H) →
    2 ≤ Open.pRank p (d1KBar p M H) →
    ∀ B N : Subgroup G, IsAGLQ p M B → B ≤ H → GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N →
      AGLCovers p H N (d1KBar p M H) → Hyp917OneAt p M H N (d1KBar p M H)

@[expose] def ElevenTwentyConcl (M : Subgroup G) : Prop :=
  ∃ H₀ : Subgroup G, GLBIsMaxTwoLocal H₀ ∧ H₀ ≠ M ∧ Open.pRank 3 (H₀ ⊓ M) = 3 ∧
    ∃ K : Subgroup (H₀ ⧸ primeComplementCore (G := H₀) 3), IsComponentOf K ⊤ ∧
      IsLinThreeFour K

theorem two_le_pRank_of_isAltTwoP {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (h : IsAltTwoP 3 K) : 2 ≤ Open.pRank 3 K := by
  obtain ⟨e⟩ := h
  rw [← CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top
    (CFSG.SectionRank.isElemAbelian_sylowThreeAlt (n := 6) le_rfl)
    (CFSG.SectionRank.card_sylowThreeAlt (n := 6) le_rfl)

omit [Finite G] in
theorem d1KBar_ne_bot_of_isAltTwoP {M H : Subgroup G} (h : IsAltTwoP 3 (d1KBar 3 M H)) :
    d1KBar 3 M H ≠ ⊥ := by
  intro hb
  have h1 := card_of_isAltTwoP_three h
  rw [hb, Subgroup.card_bot] at h1
  norm_num at h1

theorem map_eq_of_isAltTwoP {H N W : Subgroup G} (hWH : W ≤ H) (hWN : W ≤ N)
    {K₁ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    {K₂ : Subgroup (N ⧸ primeComplementCore (G := N) 3)}
    (h₁ : (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = K₁)
    (h₂ : (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) 3)) ≤ K₂)
    (hK₁ : IsAltTwoP 3 K₁) (hK₂ : IsAltTwoP 3 K₂) :
    (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) 3)) = K₂ := by
  set φ₁ : W →* H ⧸ primeComplementCore (G := H) 3 :=
    (QuotientGroup.mk' (primeComplementCore (G := H) 3)).comp (Subgroup.inclusion hWH)
  set φ₂ : W →* N ⧸ primeComplementCore (G := N) 3 :=
    (QuotientGroup.mk' (primeComplementCore (G := N) 3)).comp (Subgroup.inclusion hWN)
  have hr₁ : φ₁.range = K₁ := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, h₁]
  have hr₂ : φ₂.range =
      (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) 3)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker₂ : Nat.Coprime 3 (Nat.card φ₂.ker) := by
    have hle₂ : φ₂.ker.map (Subgroup.inclusion hWN) ≤ primeComplementCore (G := N) 3 := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hc : Nat.card (φ₂.ker.map (Subgroup.inclusion hWN)) = Nat.card φ₂.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hWN)
    rw [← hc]
    exact (primeComplementCore_coprime 3).coprime_dvd_right (Subgroup.card_dvd_of_le hle₂)
  have hle : φ₂.ker ≤ φ₁.ker := by
    obtain ⟨e⟩ := hK₁
    haveI : IsSimpleGroup (alternatingGroup (Fin (2 * 3))) :=
      alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup K₁ := e.isSimpleGroup
    set φ₁' : W →* K₁ := φ₁.codRestrict K₁ fun w => hr₁ ▸ MonoidHom.mem_range.mpr ⟨w, rfl⟩
    have hsurj : Function.Surjective φ₁' := by
      rintro ⟨y, hy⟩
      rw [← hr₁] at hy
      obtain ⟨w, rfl⟩ := hy
      exact ⟨w, rfl⟩
    have hn : (φ₂.ker.map φ₁').Normal := (MonoidHom.normal_ker φ₂).map φ₁' hsurj
    have hker : φ₁'.ker = φ₁.ker := MonoidHom.ker_codRestrict _ _ _
    haveI := hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ₂.ker.map φ₁') with h | h
    · rw [← hker]
      exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have hd : Nat.card (φ₂.ker.map φ₁') ∣ Nat.card φ₂.ker := Subgroup.card_map_dvd _ _
      rw [h, Subgroup.card_top, card_of_isAltTwoP_three ⟨e⟩] at hd
      have h3 : 3 ∣ Nat.card φ₂.ker := (by norm_num : 3 ∣ 360).trans hd
      have := Nat.Coprime.eq_one_of_dvd hker₂ h3
      norm_num at this
  have hcard₁ : Nat.card φ₁.range = 360 := by rw [hr₁]; exact card_of_isAltTwoP_three hK₁
  have hcard₂ : Nat.card K₂ = 360 := card_of_isAltTwoP_three hK₂
  have hk := Subgroup.card_ker_mul_card_range φ₁
  have hk' := Subgroup.card_ker_mul_card_range φ₂
  have hkle : Nat.card φ₂.ker ≤ Nat.card φ₁.ker := Subgroup.card_le_of_le hle
  rw [← hr₂]
  refine Subgroup.eq_of_le_of_card_ge (hr₂ ▸ h₂) ?_
  rw [hcard₂]
  have hpos : 0 < Nat.card φ₂.ker := Nat.card_pos
  rw [hcard₁] at hk
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card φ₂.ker * 360 ≤ Nat.card φ₁.ker * 360 := Nat.mul_le_mul_right _ hkle
    _ = Nat.card φ₂.ker * Nat.card φ₂.range := by rw [hk, hk']

theorem pRank_le_three_of_twoLocal (hS : Setting G) {N : Subgroup G} (hN : IsTwoLocal N) :
    Open.pRank 3 N ≤ 3 := by
  have h2 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) N hN
  rw [hS.rank] at h2
  exact h2

theorem factor_of_cover (hS : Setting G) (h9 : AGL81NineCompetitorQ G)
    (h98 : AGL81NineEightTwo G) (h984 : AGL81NineEightFour G)
    (h101 : AGL81TenOneExists G) (h115 : AGL81ElevenFiveAt G) (h3σ : 3 ∈ rankThreeSigmaA G)
    (hKR : KFactNineThreeRankOne)
    (hKA : KFactNineThreeInvolvedA6L34)
    (hKC : KFactNineThreeComponentL34) {P : Sylow 3 G} {M H R : Subgroup G}
    (he : D1Escape 3 P M H R) (hA6 : IsAltTwoP 3 (d1KBar 3 M H))
    (hcex : ¬ ElevenTwentyConcl M) {N B E : Subgroup G} (hN : GLBIsMaxTwoLocal N)
    (hNM : ¬ N ≤ M) (hB : IsAGLQ 3 M B) (hBH : B ≤ H) (hBN : B ≤ N) (hEN : E ≤ N ⊓ M)
    (hE3 : 3 ≤ Open.pRank 3 E) (hcov : AGLCovers 3 H N (d1KBar 3 M H)) :
    ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y := by
  have hg := aglGlobal_of_setting hS
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hμ := muAt_of_escape he
  have hK := exists_component_of_d1KBar_ne_bot (d1KBar_ne_bot_of_isAltTwoP hA6)
  have hat := (h9 hg 3 P M H hμ he.maxTwoLocal_H he.not_le hK B N hB hBH hN hNM hBN hcov).1
  have hKN : d1KBar 3 M N ≠ ⊥ := by
    intro hb
    have h1 := hat.kappa_le
    unfold d1Kappa at h1
    rw [hb, Subgroup.card_bot, card_of_isAltTwoP_three hA6] at h1
    norm_num at h1
  have hKN' := exists_component_of_d1KBar_ne_bot hKN
  have hN3 : 3 ≤ Open.pRank 3 N := hE3.trans (pRank_mono 3 hp (hEN.trans inf_le_left))
  obtain ⟨-, hcase⟩ := e16_of_base h9 h98 h984 h101 h115 hKR hKA hKC hS h3σ he hN hNM hB hBN hN3
    hKN'
  rcases hcase with hL34 | ⟨hA6N, -⟩
  · exfalso
    refine hcex ⟨N, hN, fun h => hNM h.le, le_antisymm ?_ (hE3.trans (pRank_mono 3 hp hEN)), _,
      isComponentOf_d1KBar_of_isLinThreeFour hKN' hL34, hL34⟩
    exact (pRank_mono 3 hp inf_le_left).trans (pRank_le_three_of_twoLocal hS hN.1)
  obtain ⟨W, hW, hWK, hWN | hfac | hlt⟩ := hat.nineSeventeen
  · have hWH : W ≤ H := hW.trans inf_le_left
    have hWN' : W ≤ N := hW.trans inf_le_right
    have hWeq := map_eq_of_isAltTwoP hWH hWN' hWK hWN hA6 hA6N
    intro x hx
    obtain ⟨m, hm, k, hk, rfl⟩ := hat.nineThree.factor x hx
    rw [← hWeq] at hk
    obtain ⟨w, hw, hwk⟩ := hk
    have ho : w⁻¹ * k ∈ primeComplementCore (G := N) 3 := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' (primeComplementCore (G := N) 3) (w⁻¹ * k) = 1
      rw [map_mul, map_inv, hwk, inv_mul_cancel]
    set o := w⁻¹ * k with hodef
    have hwoM : ((w * o * w⁻¹ : N) : G) ∈ M := by
      have : w * o * w⁻¹ ∈ primeComplementCore (G := N) 3 :=
        (primeComplementCore_normal 3).conj_mem o ho w
      exact hat.core_le ⟨_, this, rfl⟩
    refine ⟨m * ((w * o * w⁻¹ : N) : G), ⟨N.mul_mem hm.1 (w * o * w⁻¹).2, M.mul_mem hm.2 hwoM⟩,
      (w : G), hW (Subgroup.mem_subgroupOf.mp hw), ?_⟩
    have hk' : k = w * o := by rw [hodef]; group
    rw [hk']; push_cast; group
  · exact hfac
  · exfalso
    unfold d1Kappa at hlt
    rw [card_of_isAltTwoP_three hA6, card_of_isAltTwoP_three hA6N] at hlt
    exact lt_irrefl _ hlt

theorem escape_local (hS : Setting G) (h9 : AGL81NineCompetitorQ G) (h98 : AGL81NineEightTwo G)
    (h984 : AGL81NineEightFour G) (hKC : KFactNineThreeComponentL34) {P : Sylow 3 G}
    {M H R : Subgroup G} (he : D1Escape 3 P M H R) (hA6 : IsAltTwoP 3 (d1KBar 3 M H)) :
    AGL81NineAt 3 M H H ∧ Hyp111B3 3 H R (d1KBar 3 M H) ∧
      (∃ S : Sylow 3 (d1KBar 3 M H), (S : Subgroup (d1KBar 3 M H)).map (d1KBar 3 M H).subtype =
        (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ⊓
          d1KBar 3 M H) ∧
      pCoreOf 2 M ≤ pCoreOf 2 H ∧ pCoreOf 2 H ≤ M ∧ ¬ d1KBar 3 M H ≤ d1X0 3 M H := by
  have hg := aglGlobal_of_setting hS
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hμ := muAt_of_escape he
  have hK := exists_component_of_d1KBar_ne_bot (d1KBar_ne_bot_of_isAltTwoP hA6)
  have hR := isAGLQ_of_escape he
  have hatH := (h9 hg 3 P M H hμ he.maxTwoLocal_H he.not_le hK R H hR he.le_H he.maxTwoLocal_H
    he.not_le he.le_H (aglCovers_self H _)).1
  haveI := hatH.nineThree.normal
  obtain ⟨S, hS₀⟩ := he.isSylow
  have hsyl := sylowK_of_sylow (K := d1KBar 3 M H) S hS₀
  have hb3 : Hyp111B3 3 H R (d1KBar 3 M H) := by
    rcases h98 hS 3 P M H R he H R hR he.le_H he.maxTwoLocal_H he.not_le hsyl with
      hb3 | ⟨-, L, hL, hLX, hLt⟩
    · exact hb3
    · exfalso
      have h1 := hKC _ _ _ (hatH.list (d1KBar_ne_bot_of_isAltTwoP hA6)) hL (le_d1KBar hL hLX) hLt
      have h2 := card_of_isLinThreeFour h1
      rw [card_of_isAltTwoP_three hA6] at h2
      norm_num at h2
  obtain ⟨-, hOH, hHM⟩ := h984 hS 3 P M H R he H R hR he.le_H he.maxTwoLocal_H he.not_le hsyl hb3
  have hKX : ¬ d1KBar 3 M H ≤ d1X0 3 M H := by
    obtain ⟨L, hL, hLX⟩ := hK
    exact fun h => hLX ((le_d1KBar hL hLX).trans h)
  exact ⟨hatH, hb3, hsyl, hOH, hHM, hKX⟩

theorem cfgData_of_escape (hS : Setting G) (h9 : AGL81NineCompetitorQ G)
    (h98 : AGL81NineEightTwo G) (h984 : AGL81NineEightFour G)
    (h101 : AGL81TenOneExists G) (h115 : AGL81ElevenFiveAt G) (h3σ : 3 ∈ rankThreeSigmaA G)
    (hKR : KFactNineThreeRankOne)
    (hKA : KFactNineThreeInvolvedA6L34)
    (hKC : KFactNineThreeComponentL34) {P : Sylow 3 G} {M H R : Subgroup G}
    (he : D1Escape 3 P M H R) (hA6 : IsAltTwoP 3 (d1KBar 3 M H))
    (hcex : ¬ ElevenTwentyConcl M) : AGL81CfgData 3 P M H R (d1KBar 3 M H) := by
  obtain ⟨hatH, hb3, hsyl, hOH, hHM, hKX⟩ := escape_local hS h9 h98 h984 hKC he hA6
  have hR := isAGLQ_of_escape he
  have hfac : AGLCompetitorFactorAt 3 M H (d1KBar 3 M H) R := fun N hN hNM hRN hcov =>
    factor_of_cover hS h9 h98 h984 h101 h115 h3σ hKR hKA hKC he hA6 hcex hN hNM hR he.le_H
      hRN (le_inf hRN he.le_M) he.three_le_pRank hcov
  exact ⟨⟨H, R, he⟩, he.maxTwoLocal_H, hR, he.le_H, he.not_le, hKX, hatH.core_le, rfl, hb3, hsyl,
    fun T hT hT1 => star_of_factorAt Nat.prime_three (by norm_num) he.maxTwoLocal_M.1
      he.maxTwoLocal_H hKX hOH hHM hatH.core_le hatH.nineThree.factor hR he.le_H hfac hb3 hT hT1⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
