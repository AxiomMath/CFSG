module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenThreeInspection
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem AGL81CfgData.nineEightFour' (hS : Setting G) (h98 : AGL81NineEightFour G) {p : ℕ}
    {P : Sylow p G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) :
    pCoreOf 2 (H ⊓ M) = pCoreOf 2 H ∧ pCoreOf 2 M ≤ pCoreOf 2 H ∧ pCoreOf 2 H ≤ M := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hb3 := hd.b3
  have hsy := hd.sylowK
  rw [hd.kbar] at hb3 hsy
  exact h98 hS p P M H₁ R₁ hesc H Q hd.base hd.le_H hd.maxH hd.not_le hsy hb3

theorem AGL81CfgData.toTwoLocalPhaseThree' (hS : Setting G) (h98 : AGL81NineEightFour G)
    {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K) :
    TwoLocalPhaseThree M H := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  obtain ⟨h1, -, h3⟩ := hd.nineEightFour' hS h98
  exact
    { maxTwoLocal_M := hesc.maxTwoLocal_M
      maxTwoLocal_H := hd.maxH
      not_le := hd.not_le
      twoCore_le := h3
      charTwo_M := hS.charTwo M hesc.maxTwoLocal_M.1
      twoCore_inf := h1 }

variable (G) in
@[expose] def AGL81TenThreeThreeCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (L.subgroupOf M).Normal → ∀ B : Subgroup G, B ≤ H ⊓ M → IsPGroup p B →
      (∀ b ∈ B, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
      (∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) ∨
        ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open Subgroup

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81ElevenThreeInspectionCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (L.subgroupOf M).Normal → ∀ B : Subgroup G, B ≤ H ⊓ M → IsPGroup p B →
    ∀ T : Subgroup G, T ≤ jZero H L → IsPGroup 2 T → ¬ 2 ∣ T.relIndex (jZero H L) →
    B ≤ normalizer (T : Set G) →
    2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L →
    ¬ (∀ b ∈ B, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
    p = 3 ∧ (∃ N : ℕ, 10 ≤ N ∧ Even N ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin N))) ∧
    ∃ I₀ ∈ cZero (H ⊓ L), Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* alternatingGroup (Fin 5))

variable {G}

theorem agl81ElevenThreeInspectionCfg_of (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : NoXBlockFor G) (h98 : AGL81NineEightFour G) (hA7 : AGL81TenNineOneCfg G)
    (hPS : KFactParabolicSyl) (hTr : KFactSylNormTriv) (hSy : KFactSylNormSym)
    (hSyP : KFactSylNormSymProd) : AGL81ElevenThreeInspectionCfg G := by
  intro hS p P M H Q K hd L hL hLn B hBHM hB T hTJ hT2 hTi hBT heven hnt
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  exact elevenThreeInspection_core h85 h93 hNX hPS hTr hSy hSyP hS hesc.prime hesc.ne_two
    (hd.toTwoLocalPhaseThree' hS h98) (hd.nineEightFour' hS h98).2.1 hL hLn
    (hA7 hS p P M H Q K hd L hL) hBHM hB hTJ hT2 hTi hBT heven hnt

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
