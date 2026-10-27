module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Layer
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TwoLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G]

theorem d2L34BetaLayerExists3_of_core
    (hcore : AGL81II1320Core) (hFF : CitedFFL34BestOffender)
    (hN : D2L34BetaNormalizerSolvable3 G) (hX : D1NoXBlock3 G) : D2L34BetaLayerExists3 G := by
  intro d P M A H R Rbar K ctx hstr hKmax hcon
  have := ctx.amb
  have hc := ctx.conf
  have hAll := ctx.allResidue
  have hNX : NoXBlockFor G := noXBlockFor_of_setting hX ctx.setting
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOnly := hAll.onlyL34At
  obtain ⟨T, hT, -⟩ := B6.exists_isSylowTwoOf_ge (J := H ⊓ M) (X := ⊥) IsPGroup.of_bot bot_le
  obtain ⟨hTM, -⟩ := D2L34BetaConf3.isSylowTwoOf_of_cover hFF hc hstr hOnly hT
  obtain ⟨x, -, hxN, hxM, -⟩ := D2L34BetaConf3.exists_two_element hc hT
  have hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M := fun hle => hxM (hle hxN)
  have hMtop : M ≠ ⊤ := fun h => hNT (h ▸ le_top)
  refine hcore G M T (D2Amb3.glob (G := G)).kProper hMtop
    ((D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1) hTM
    (fun C hC1 hCT hchar => hN d P M A H R Rbar K ctx hstr hKmax T hTM C hC1 hCT hchar)
    (fun C hC1 hCT hchar U hU hU3 hUc => ?_)
    (fun Y hYM hYs hYX => hNX M Y hc.esc.maxTwoLocal_M hYM hYs hYX) hcon
  have hNC : IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hC1, hTM.2.1.to_le hCT, rfl⟩
  have hNCM : ¬ Subgroup.normalizer (C : Set G) ≤ M := fun hle =>
    hNT ((normalizer_le_normalizer_of_char hCT hchar).trans hle)
  exact D2L34BetaConf3.exists_conj_eq_of_not_isCyclic hc hstr hOnly hNC hNCM
    (hU.trans inf_le_left) (hU.trans inf_le_right) hU3 hUc

end CFSG.LocalAnalysis.RankThreeTheoremC
