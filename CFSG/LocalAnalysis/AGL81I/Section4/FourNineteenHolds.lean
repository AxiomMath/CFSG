module

public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteen
public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteenArith
public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteenParab
public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteenSmall
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankAlt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankSmall
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwoSpinMinus

public section

namespace CFSG.LocalAnalysis.AGL81I.Section4

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime CFSG.LocalAnalysis.RankThreeUC.S15

theorem agl81FourNineteen_holds
    : AGL81FourNineteen := by
  intro Y GY FY hY hcl T J hT hNJ hJ hJtop p hpprime hp5 hpJ h3
  let I : ParabInputs :=
    ⟨parabCore_of_model_psu, parabCore_of_model_psl_two, parabCore_of_model_psu_two,
      parabCore_of_model_psp_two, parabCore_of_model_pomegaPlus_two,
      parabCore_of_model_pomegaMinus_two⟩
  have hG : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hChev : LieOddRankChev :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev hG
  have hAlt : LieOddRankAlt := lieOddRankAlt_holds
  have hSmall : LieOddRankSmall := lieOddRankSmall_of_griess hG
  rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · have hnot := not_dvd_sq_sub_one_of_isClassicalTwoOrG2 I d hd e hT hNJ hJ
      hpprime hp5 hpJ
    have hp3 := hChev Y hY d hd ⟨e⟩ 3 Nat.prime_three (by norm_num)
    have hpd := hChev Y hY d hd ⟨e⟩ p hpprime (by omega)
    have h3' : mRankChev d.1 3 (Nat.card (Subgroup.center Y)) ≤ 3 := by
      rw [hp3] at h3
      exact h3
    have harith := mRankChev_add_one_le d.2 hd hpprime hp5 hnot h3'
    rw [hpd, hp3]
    exact harith
  · exact pRank_add_one_le_of_alt hAlt hY hn e hpprime hp5
  · exact pRank_add_one_le_of_small hSmall hY d hd e hpprime hp5

end CFSG.LocalAnalysis.AGL81I.Section4

end
