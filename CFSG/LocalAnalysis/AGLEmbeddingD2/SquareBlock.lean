module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareDispatch
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.SquareDispatch


theorem kFactBlockAltFiveSquareParabolic_of (h86 : Asc81bEightSix)
    (hTL : CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLie) (hSp : SquareSpFamily)
    (hSU : SquareSUFamily) (hDp : SquareSpinPlusFamily) (hDm : SquareSpinMinusFamily) :
    KFactBlockAltFiveSquareParabolic := by
  intro G _ _ M S L U hK hA hL hX hS hB h2 hUM hUN hUL φ hφ hφ1
  obtain ⟨hcl, T, J, hT, hNJ, -, hJtop, hJ⟩ := BlockCyc.nineThreeTwo_parabolic hA hL hS h2
  have hSL := h86 G M S hK hA _ hL.component
  have hQ := InnerStep.hasSubquotient_parabImage hSL hB hUM hUN hUL φ hφ hφ1
  rw [← hJ] at hQ
  have hq : CFSG.IsQuasisimple ↥(barM M L) := isQuasisimple_of_open' hL.component.2.2
  obtain ⟨T', hT'⟩ := exists_sylow_of_isSylowTwoOf_top hT
  have h3 := three_le_pRank_of_classical hTL hSp hSU hDp hDm hq hcl T' J (hT' ▸ hNJ) hJtop hQ
  have hcomap : J.comap (QuotientGroup.mk' (Subgroup.center ↥(barM M L))) =
      (blockPL M S L).subgroupOf (barM M L) := by
    rw [hJ, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.2 (center_le_blockPL_of_nineThreeTwo h2)]
  rw [hcomap] at h3
  refine h3.trans ?_
  have h := SectionRank.pRank_le_map (p := 3) (by norm_num) (barM M L).subtype
    (barM M L).subtype_injective ((blockPL M S L).subgroupOf (barM M L))
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h2.2.1.1] at h

end CFSG.AGLEmbeddingD2
