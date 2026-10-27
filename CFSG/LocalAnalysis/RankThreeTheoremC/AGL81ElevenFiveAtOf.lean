module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenCfgChain
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenThreeAt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactL34ThreeRankTwo : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), IsLinThreeFour K → 2 ≤ Open.pRank 3 K

variable (G) in
@[expose] def AGL81ElevenElevenOtherCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p →
    (Open.pRank p K ≤ 1 → 3 ≤ Open.pRank p H) → ¬ (p = 3 ∧ IsAltTwoP 3 K) →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ¬ AGL81ElevenFiveOne p H K L →
      ∃ A : Subgroup G, A ≤ H ∧ IsAGLQ p M A ∧
        (∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
          (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K) ∧
        ⁅A, L⁆ ≤ pCoreOf 2 L ∧ (2 ≤ Open.pRank p K → A = d1LiftX p H Q K)

theorem AGL81ElevenData.toCfgAt {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81ElevenData p P M H Q K)
    {A : Subgroup G} (hA : IsAGLQ p M A) (hAH : A ≤ H)
    (hsylA : ∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K)
    (hb3A : Hyp111B3 p H A K) : AGL81CfgData p P M H A K := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  exact ⟨hd.escape, hd.maxH, hA, hAH, hd.pair.not_le, hd.pair.not_le_X0, hd.pair.primeCore_le,
    hd.kbar, hb3A, hsylA, fun R hR hR1 =>
      star_of_pair hesc.prime hesc.ne_two (hd.pair.rebase hA hAH) hb3A hR hR1⟩

theorem AGL81ElevenData.sylowK_d1LiftX {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81ElevenData p P M H Q K) :
    ∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
      ((d1LiftX p H Q K).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K := by
  obtain ⟨S, hS'⟩ := hd.sylowK
  refine ⟨S, ?_⟩
  rw [map_d1LiftX, inf_assoc, inf_idem]
  exact hS'

theorem AGL81ElevenData.nineThree (h9 : AGL81NineCompetitorQ G) (hS : Setting G) {p : ℕ}
    {P : Sylow p G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81ElevenData p P M H Q K) :
    d1PlusCore p H K ≤ M ∧ NineThreeListGroup p K := by
  have hk := hd.kbar
  subst hk
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hne : d1KBar p M H ≠ ⊥ := fun h => hd.pair.not_le_X0 (by rw [h]; exact bot_le)
  have h1 := (h9 (aglGlobal_of_setting hS) p P M H (muAt_of_escape hesc) hd.maxH hd.pair.not_le
    (exists_component_of_d1KBar_ne_bot hne) Q H hd.pair.base hd.pair.le_H hd.maxH
    hd.pair.not_le hd.pair.le_H (aglCovers_self H _)).1
  exact ⟨h1.nineThree.plusCore_le, h1.list hne⟩

theorem AGL81ElevenData.b3_or_isLinThreeFour (h98 : AGL81NineEightTwo G)
    (hKC : KFactNineThreeComponentL34) (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81ElevenData p P M H Q K) (hlist : NineThreeListGroup p K) {A : Subgroup G}
    (hA : IsAGLQ p M A) (hAH : A ≤ H)
    (hsylA : ∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K) :
    Hyp111B3 p H A K ∨ (p = 3 ∧ IsLinThreeFour K) := by
  have hk := hd.kbar
  subst hk
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  rcases h98 hS p P M H₁ R₁ hesc H A hA hAH hd.maxH hd.pair.not_le hsylA with
    hb3 | ⟨hp3, L', hL', hLX, hLt⟩
  · exact Or.inl hb3
  · subst hp3
    exact Or.inr ⟨rfl, hKC _ _ _ hlist hL' (le_d1KBar hL' hLX) hLt⟩

theorem AGL81ElevenData.false_of_rebase (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81ElevenData p P M H Q K) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (hXM : d1PlusCore p H K ≤ M) {A : Subgroup G} (hAH : A ≤ H) (hA : IsAGLQ p M A)
    (hsylA : ∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K)
    (hb3A : Hyp111B3 p H A K) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hLn : (L.subgroupOf M).Normal) (hAL : ⁅A, L⁆ ≤ pCoreOf 2 L) : False := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hdA := hd.toCfgAt hA hAH hsylA hb3A
  have hglob : AGLGlobal G := aglGlobal_of_setting hS
  have hM : GLBIsMaxTwoLocal M := hesc.maxTwoLocal_M
  have hAM : A ≤ M := hA.1
  have hHn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := localGroup_le_normalizer_pCoreOf 2 H
  have hAS : A ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := hAH.trans hHn
  obtain ⟨R, hSR, hR⟩ := TwoRest3A6.exists_isMaxInvariantTwoIn_ge
    (hb3A _ (pCoreOf_isPGroup 2 H) (pCoreOf_le 2 H) hAS) (pCoreOf_isPGroup 2 H) hAS
  have hR1 : R ≠ ⊥ := fun h0 => pCoreOf_two_ne_bot hd.maxH.1 (le_bot_iff.mp (h0 ▸ hSR))
  obtain ⟨hCGS, hRmax⟩ := hdA.star R hR hR1
  have hRM : R ≤ M := hR.1.trans hXM
  have hR2 : IsPGroup 2 R := hR.2.1
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRM.trans hMn
  have hMM : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := localGroup_le_normalizer_pCoreOf 2 M
  have hOR : pCoreOf 2 M ≤ R :=
    TwoRest3A6.le_of_isMaxInvariantTwo hRmax (pCoreOf_isPGroup 2 M) (hRM.trans hMM)
      (hAM.trans hMM)
  have hOLM : pCoreOf 2 L ≤ pCoreOf 2 M := F7.pCoreOf_mono_of_le_normalizer hL.le hMn
  have hc : ∀ b ∈ A, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M := fun b hb l hl => by
    have h1 := Subgroup.commutator_mem_commutator hb hl
    rw [commutatorElement_def] at h1
    exact hOLM (hAL h1)
  have hsylL := TwoRest3A6.not_two_dvd_index_inf_of_isMaxInvariantTwo hRmax hOR hRL hc
  exact hL.not_le_normalizer ((le_of_normal_block_of_local hglob hCGT hD2 hM hd.pair.not_le hL.le
    hLn hRM hR2 hOR hRL hsylL (normalizer_le_of_cgs_le hCGS)).trans hHn)

theorem AGL81ElevenData.isComponentOf_of_simple {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81ElevenData p P M H Q K)
    (hs : IsSimpleGroup K) : IsComponentOf K ⊤ := by
  have hk := hd.kbar
  subst hk
  have hne : d1KBar p M H ≠ ⊥ := fun h => hd.pair.not_le_X0 (by rw [h]; exact bot_le)
  exact isComponentOf_d1KBar (exists_component_of_d1KBar_ne_bot hne) hs

theorem isSimpleGroup_of_isAltTwoP_three {K : Type} [Group K] (h : IsAltTwoP 3 K) :
    IsSimpleGroup K := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin (2 * 3))) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact e.isSimpleGroup

end CFSG.LocalAnalysis.RankThreeTheoremC
