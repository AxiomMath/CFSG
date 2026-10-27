module

public import CFSG.LocalAnalysis.RankThreeUC.GN15LayerFinal
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.Final
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreePrimeJCentralProved

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem gnAbsorbs_H_holds
    (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂) : GNAbsorbs T T₁ T₂ (gnHPre T) :=
  gnAbsorbs_H CFSG.HardMathSupport.Meierfrankenfeld.AGL81.agl81I59
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.threePrimeJCentral_proved hX hP

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
