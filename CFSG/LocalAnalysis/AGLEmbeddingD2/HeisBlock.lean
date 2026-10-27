module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisDispatch

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.HeisDispatch
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)


theorem kFactBlockFiveHeisParabolic_of (h86 : Asc81bEightSix) (hGA : GriessMultipliersAllModels)
    (hL : HeisLinearFamily) (hSp : HeisSpFamily) (hSU : HeisSUFamily)
    (hDp : HeisSpinPlusFamily) (hDm : HeisSpinMinusFamily) (hG2 : HeisG2Family) :
    KFactBlockFiveHeisParabolic := by
  intro G _ _ M S L U hK hA hL' hX hS hB h2 hUM hUN hUL hU125 hUnc hUbot
  obtain ⟨hcl, T, J, hT, hNJ, -, hJtop, hJ⟩ := BlockCyc.nineThreeTwo_parabolic hA hL' hS h2
  have hSL := h86 G M S hK hA _ hL'.component
  have hQ := InnerStep.hasSubquotient_parabImage hSL hB hUM hUN hUL (MonoidHom.id U)
    Function.surjective_id (fun u hu => by rw [hUbot] at hu; exact Subgroup.mem_bot.mp hu)
  rw [← hJ] at hQ
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hU5 : IsPGroup 5 U := IsPGroup.of_card hU125
  obtain ⟨P, hPJ, hP, hPc⟩ := HeisEngine.exists_nonabelian_of_hasSubquotient hU5 hUnc hQ
  have hq : CFSG.IsQuasisimple ↥(barM M L) := isQuasisimple_of_open' hL'.component.2.2
  obtain ⟨T', hT'⟩ := exists_sylow_of_isSylowTwoOf_top hT
  have h5 := three_le_pRank_five_of_classical hGA hL hSp hSU hDp hDm hG2 hq hcl T' J
    (hT' ▸ hNJ) hJtop hPJ hP hPc
  have hcomap : J.comap (QuotientGroup.mk' (Subgroup.center ↥(barM M L))) =
      (blockPL M S L).subgroupOf (barM M L) := by
    rw [hJ, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.2 (center_le_blockPL_of_nineThreeTwo h2)]
  rw [hcomap] at h5
  refine h5.trans ?_
  have h := SectionRank.pRank_le_map (p := 5) (by norm_num) (barM M L).subtype
    (barM M L).subtype_injective ((blockPL M S L).subgroupOf (barM M L))
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h2.2.1.1] at h

end CFSG.AGLEmbeddingD2
