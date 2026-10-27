module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisBlock
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisLinear
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSymplectic
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisUnitary
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinPlus
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinMinus
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisG2
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.HeisDispatch

theorem heisLinearFamily_holds : HeisLinearFamily :=
  fun _ _ _ _ _ _ _ _ e _ _ _ ρ hρ hρker h5 T J hNJ hJ P hPJ hP hPc =>
    HeisLinear.three_le_pRank_five_sl e ρ hρ hρker h5 T J hNJ hJ P hPJ hP hPc

theorem heisSpFamily_holds : HeisSpFamily :=
  fun _ _ _ _ _ _ _ _ e _ _ _ ρ hρ hρker h5 T J hNJ hJ P hPJ hP hPc =>
    HeisSymplectic.three_le_pRank_five_sp e ρ hρ hρker h5 T J hNJ hJ P hPJ hP hPc

theorem heisSUFamily_holds : HeisSUFamily :=
  fun _ _ _ _ _ _ hF hn _ _ _ e _ _ _ ρ hρ hρker h5 T J hNJ hJ P hPJ hP hPc =>
    HeisUnitary.three_le_pRank_five_su hF hn e ρ hρ hρker h5 T J hNJ hJ P hPJ hP hPc

theorem heisSpinPlusFamily_holds : HeisSpinPlusFamily :=
  fun _ _ _ _ _ hn _ _ _ e _ _ _ ρ hρ hρker h5 T J hNJ hJ P hPJ hP hPc =>
    HeisSpinPlus.three_le_pRank_five_spinPlus hn e ρ hρ hρker h5 T J hNJ hJ P hPJ hP hPc

theorem heisSpinMinusFamily_holds : HeisSpinMinusFamily :=
  fun _ _ _ _ _ _ _ hirr hn _ _ _ e _ _ _ ρ hρ hρker h5 T J hNJ hJ P hPJ hP hPc =>
    HeisSpinMinus.three_le_pRank_five_spinMinus hirr hn e ρ hρ hρker h5 T J hNJ hJ P hPJ hP hPc

theorem heisG2Family_holds :
    HeisG2Family :=
  fun _ _ _ _ _ _ _ e T J hNJ hJ P hPJ hP =>
    HeisG2.isMulCommutative_of_isPGroup_five_g2 e T J hNJ hJ P hPJ hP


theorem kFactBlockFiveHeisParabolic_holds : KFactBlockFiveHeisParabolic :=
  kFactBlockFiveHeisParabolic_of
    (asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved)
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds heisLinearFamily_holds
    heisSpFamily_holds heisSUFamily_holds heisSpinPlusFamily_holds heisSpinMinusFamily_holds
    heisG2Family_holds

end CFSG.AGLEmbeddingD2
