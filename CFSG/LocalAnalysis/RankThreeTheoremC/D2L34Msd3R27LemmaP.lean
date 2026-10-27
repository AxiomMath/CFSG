module

import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3CyclicInt
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNoncycA
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G] {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
  {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34SideCtx3.normalizer_zpowers_le_of_escape
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) {E N : Subgroup G}
    (hesc : D2Escape 3 P M E N E) {x : G} (hxN : x ∈ N) (hxM : x ∈ M) (hx : orderOf x = 3) :
    Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨n, -, hnx⟩ : ∃ n ∈ N, n * x * n⁻¹ ∈ E := by
    obtain ⟨T, hT⟩ := hesc.isSylow
    have hxp' : IsPGroup 3 ((Subgroup.zpowers x).subgroupOf N) := hxp.comap_subtype
    obtain ⟨S, hS⟩ := hxp'.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N S T
    have hxS : (⟨x, hxN⟩ : N) ∈ S := hS (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x))
    have hgx : g * ⟨x, hxN⟩ * g⁻¹ ∈ ((g • S : Sylow 3 N) : Set N) := by
      rw [@Sylow.coe_smul 3 N _ g S]
      exact ⟨⟨x, hxN⟩, hxS, rfl⟩
    rw [hg] at hgx
    refine ⟨g, g.2, ?_⟩
    rw [← hT]
    exact ⟨g * ⟨x, hxN⟩ * g⁻¹, hgx, by simp⟩
  have hy1 : Subgroup.zpowers (n * x * n⁻¹) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    apply hx1
    calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  have hNy := hesc.normalizer_le_of_le_A (Subgroup.zpowers_le.mpr hnx) hy1
  have hmap : (Subgroup.zpowers x).map (MulAut.conj n).toMonoidHom =
      Subgroup.zpowers (n * x * n⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hNmap : (Subgroup.normalizer (Subgroup.zpowers x : Set G)).map
      (MulAut.conj n).toMonoidHom ≤ M := by
    rw [← CFSG.AGLEmbeddingD2.normalizer_map_conj, hmap]
    exact hNy
  have hnM : n ∈ M := by
    by_contra hnM
    have h1 := ctx.pRank_inf_conj_le_one hnM
    have hle : M ⊓ Subgroup.centralizer ({x} : Set G) ≤ M ⊓ GLBConj n M := by
      intro g hg
      refine ⟨hg.1, n * g * n⁻¹,
        hNmap ⟨g, centralizer_singleton_le_normalizer_zpowers x hg.2, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    obtain ⟨W, hWM, hWp, hWidx, hxW⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.exists_sylow_le (Subgroup.zpowers_le.mpr hxM) hxp
    obtain ⟨F, hFW, hFel, hF27⟩ := ctx.exists_E27_le_sylow hWM hWp hWidx
    have hW2 : 2 ≤ CFSG.Open.pRank 3 W :=
      (by norm_num : 2 ≤ 3).trans
        (CFSG.SectionRank.le_pRank (by norm_num) hFW hFel (by rw [hF27]; norm_num))
    have h2 := two_le_pRank_inf_centralizer hWp hW2 (hxW (Subgroup.mem_zpowers x)) hx1
      (hx ▸ pow_orderOf_eq_one x)
    have h3 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
      ((inf_le_inf_right _ hWM).trans hle)
    omega
  exact CFSG.AGLEmbedding.le_of_map_conj_le hnM hNmap

end CFSG.LocalAnalysis.RankThreeTheoremC
