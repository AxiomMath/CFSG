module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WGood

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

variable {G : Type} [Group G] [Finite G]

theorem exists_E9_le_of_not_isCyclic {Y : Subgroup G} (hYp : IsPGroup 3 Y) (hYc : ¬ IsCyclic Y) :
    ∃ E : Subgroup G, E ≤ Y ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : 2 ≤ CFSG.Open.pRank 3 Y :=
    two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hYp hYc
  obtain ⟨F, hFY, hFel, hFc⟩ := pRank_attained 3 Nat.prime_three Y
  obtain ⟨E₀, hE₀F, hE₀, hE₀c⟩ := exists_sub_ea_of_dvd (isEA3_of_isElemAbelian hFel) (n := 2)
    (by rw [hFc]; exact pow_dvd_pow 3 h2)
  exact ⟨E₀, hE₀F.trans hFY, isElemAbelian_of_isEA3 hE₀, by rw [hE₀c]; norm_num⟩

theorem exists_normal_E9_of_noncyclic {W D : Subgroup G} (hWp : IsPGroup 3 W) (hDW : D ≤ W)
    (hDN : W ≤ Subgroup.normalizer (D : Set G)) (hDc : ¬ IsCyclic D) :
    ∃ E : Subgroup G, E ≤ D ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      W ≤ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDp : IsPGroup 3 D := hWp.to_le hDW
  obtain ⟨E₀, hE₀D, hE₀el, hE₀c9⟩ := exists_E9_le_of_not_isCyclic hDp hDc
  have hE₀ := isEA3_of_isElemAbelian hE₀el
  have hE₀c : Nat.card E₀ = 3 ^ 2 := by rw [hE₀c9]; norm_num
  have hDnormal : (D.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDW).mpr hDN
  obtain ⟨N, hND, hNn, hNea, hNc⟩ := (qstmt_succ 1 le_rfl (by norm_num) qstmt_one) ↥W hWp
    (D.subgroupOf W) hDnormal
    ⟨E₀.subgroupOf W, Subgroup.comap_mono hE₀D,
      ⟨fun a ha b hb => Subtype.ext (hE₀.1 _ ha _ hb), fun a ha => Subtype.ext (hE₀.2 _ ha)⟩,
      by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE₀D.trans hDW)).toEquiv, hE₀c]⟩
  set E : Subgroup G := N.map W.subtype with hE
  have hEW : E ≤ W := Subgroup.map_subtype_le N
  have hEsub : E.subgroupOf W = N := Subgroup.comap_map_eq_self_of_injective W.subtype_injective N
  have hED : E ≤ D := by
    rintro _ ⟨n, hn, rfl⟩
    exact hND hn
  refine ⟨E, hED, ?_, ?_, ?_⟩
  · refine isElemAbelian_of_isEA3 ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      exact congrArg Subtype.val (hNea.1 x hx y hy)
    · obtain ⟨x, hx, rfl⟩ := ha
      exact congrArg Subtype.val (hNea.2 x hx)
  · rw [hE, Subgroup.card_map_of_injective W.subtype_injective, hNc]
    norm_num
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hEW).mp (hEsub ▸ hNn)

section Ctx

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34SideCtx3.hasGoodE9_of_noncyclic_normal
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {W D F : Subgroup G} (hWM : W ≤ M)
    (hWp : IsPGroup 3 W) (hDW : D ≤ W) (hDN : W ≤ Subgroup.normalizer (D : Set G))
    (hDc : ¬ IsCyclic D) (hFW : F ≤ W) (hFel : IsElemAbelian 3 F) (hF27 : Nat.card F = 27) :
    HasGoodE9 M D := by
  obtain ⟨E, hED, hEel, hE9, hWE⟩ := exists_normal_E9_of_noncyclic hWp hDW hDN hDc
  exact h.hasGoodE9_of_normalizes hED (hED.trans (hDW.trans hWM)) hEel hE9 (hFW.trans hWM) hFel
    hF27 (hFW.trans hWE)

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC
