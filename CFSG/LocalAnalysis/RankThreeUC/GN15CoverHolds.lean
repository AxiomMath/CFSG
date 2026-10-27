module

public import CFSG.LocalAnalysis.RankThreeUC.GN15CoverP
public import CFSG.LocalAnalysis.RankThreeUC.GN15CoverSec
public import CFSG.LocalAnalysis.RankThreeUC.GN15LayerHolds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNInputRed

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem gnCoverP_of_JOutCentral (hI59 : AGL81I59) (hJ3 : ThreePrimeJCentral) (hJ : JOutCentral)
    (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂) : GNCoverP T T₁ T₂ :=
  gnCoverP_of_JOutCentralAt hI59 hJ3 (hJ X T hX) hX hP

theorem gnCoverSec_of_JOutCentral (hI59 : AGL81I59) (hJ3 : ThreePrimeJCentral) (hJ : JOutCentral)
    (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂) : GNCoverSec T T₁ T₂ :=
  gnCoverSec_of_JOutCentralAt hI59 hJ3 (hJ X T hX) hX hP

theorem gnCoverP_holds
    (hJ : JOutCentral) (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂) : GNCoverP T T₁ T₂ :=
  gnCoverP_of_JOutCentral CFSG.HardMathSupport.Meierfrankenfeld.AGL81.agl81I59
    threePrimeJCentral_proved hJ hX hP

theorem gnCoverSec_holds
    (hJ : JOutCentral) (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂) : GNCoverSec T T₁ T₂ :=
  gnCoverSec_of_JOutCentral CFSG.HardMathSupport.Meierfrankenfeld.AGL81.agl81I59
    threePrimeJCentral_proved hJ hX hP

theorem factor_of_JOutCentral
    (hJ : JOutCentral) : GNInputRed.Factor := by
  intro X _ _ T hX _ T₁ T₂ hP
  exact ⟨gnFactor_of_absorbs_H hJ hX hP (gnAbsorbs_H_holds hX hP), gnCoverP_holds hJ hX hP,
    gnCoverSec_holds hJ hX hP⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
