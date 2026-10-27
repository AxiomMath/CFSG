module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

structure CenterInSitu {Y : Type} [Group Y] (p : ℕ) (T Y₀ : Subgroup Y) : Prop where
  primeCore : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    p.Coprime (Nat.card W) → W = ⊥
  normal_dichotomy : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    W = ⊥ ∨ centerOf T ≤ W
  centralizer_le : Y₀ ⊓ Subgroup.centralizer (centerOf T : Set Y) ≤ T
  center_ne : centerOf T ≠ ⊥

theorem D1Extremal.survivorData_center {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M H R : Subgroup G} (hext : D1Extremal p P M H R)
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G)
    (hS : CenterInSitu p ((R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))) :
    D1SurvivorData p P M H R (centerOf R) := by
  have hRH : R ≤ H := hext.le_H
  have hRp : IsPGroup p R := hext.isPGroup
  have hmap := map_inf_centralizer_eq (p := p) hRH hRp
  have hZb : ((centerOf R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      centerOf ((R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) := hmap
  refine hext.survivorData_of_map hglob inf_le_left ?_ (fun W hW hWn hWc => ?_) ?_ ?_
  · intro hbot
    apply hS.center_ne
    rw [← hZb, hbot, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  · exact hS.primeCore W hW ((Subgroup.normal_subgroupOf_iff_le_normalizer hW).mp hWn) hWc
  · intro W hW hWn
    rw [hZb]
    exact hS.normal_dichotomy W hW hWn
  · rw [hZb]
    exact hS.centralizer_le

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactSp48Local : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsSpFourEightIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 3 Y) (Y₀ : Subgroup Y),
      3 ≤ Open.pRank 3 (T : Subgroup Y) → GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ →
      CenterInSitu 3 (T : Subgroup Y) Y₀ ∧ centerOf (T : Subgroup Y) ≤ K

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem le_of_map_le_of_isPGroup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H R A U : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup p R) (hAR : A ≤ R) (hUR : U ≤ R)
    (hle : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      (U.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) : A ≤ U := by
  have hp : p.Prime := Fact.out
  intro a ha
  obtain ⟨u, hu, hua⟩ := hle (Subgroup.mem_map_of_mem _
    (show (⟨a, hRH (hAR ha)⟩ : H) ∈ A.subgroupOf H from ha))
  have hN : ((u⁻¹ * ⟨a, hRH (hAR ha)⟩ : H) : G) ∈ GLBPrimeCore p H := by
    rw [mem_glbPrimeCore_iff_mk_eq_one, map_mul, map_inv, hua, inv_mul_cancel]
  have hRm : ((u⁻¹ * ⟨a, hRH (hAR ha)⟩ : H) : G) ∈ R :=
    R.mul_mem (R.inv_mem (hUR (Subgroup.mem_subgroupOf.mp hu))) (hAR ha)
  have hbot := inf_eq_bot_of_isPGroup hp hR (glbPrimeCore_coprime p H)
  have h1 : ((u⁻¹ * ⟨a, hRH (hAR ha)⟩ : H) : G) = 1 := by
    have hmem : ((u⁻¹ * ⟨a, hRH (hAR ha)⟩ : H) : G) ∈ R ⊓ GLBPrimeCore p H := ⟨hRm, hN⟩
    rwa [hbot, Subgroup.mem_bot] at hmem
  have h2 : a = (u : G) := by
    have : (u : G)⁻¹ * a = 1 := by simpa using h1
    rw [inv_mul_eq_one] at this
    exact this.symm
  rw [h2]
  exact Subgroup.mem_subgroupOf.mp hu

theorem stmtSp48Surv_of (hK : KFactSp48Local) : StmtSp48Surv := by
  intro G _ _ _ d hd T _ _ eT P M H R U h
  obtain ⟨K, hKn, ⟨eK⟩, hC, hUK⟩ := h.socle
  obtain ⟨eT⟩ := eT
  obtain ⟨Rbar, hRbar, hred⟩ := h.ext.reducedNongeneration
  obtain ⟨hS, hZK⟩ := hK _ K d hd hKn ⟨eK.trans eT⟩ hC Rbar _ hred.three_le_pRank
    hred.weakCore_le hred.ne_top
  rw [hRbar] at hS hZK
  refine ⟨h.ext.survivorData_center h.glob hS, ?_⟩
  have hmap := map_inf_centralizer_eq (p := 3) h.ext.le_H h.ext.isPGroup
  refine le_of_map_le_of_isPGroup h.ext.le_H h.ext.isPGroup inf_le_left h.le_R ?_
  rw [hUK]
  exact le_inf (Subgroup.map_mono (Subgroup.comap_mono inf_le_left)) (hmap ▸ hZK)

end CFSG.AGLEmbedding
