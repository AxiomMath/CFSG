module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrFusionBridge
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrIsolatedFourEscape
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.ComponentClassification.UnbalancedCorr (GSMaximalComponent)

namespace HeKM

noncomputable def centerQuotEquivOfSurjective {P Q : Type*} [Group P] [Group Q]
    (hP : Group.IsPerfect P) (f : P →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ center P) : P ⧸ center P ≃* Q ⧸ center Q :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      LocalCores.comap_center_eq_of_perfect hP f hf hker])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (center Q)).comp f)
      ((QuotientGroup.mk'_surjective _).comp hf))

end HeKM

end CFSG.ComponentClassification.GrSLit
