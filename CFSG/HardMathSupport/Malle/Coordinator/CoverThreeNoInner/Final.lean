module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Assembly
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.FieldReplaceUnitary
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.DiagLinearFinal
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.DiagUnitary

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.AGLEmbedding

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels) in
theorem p1OffCharCoverThreeNoInner_of_fieldUnitary
    (hGA : GriessMultipliersAllModels) (hFU : CoverThreeNoInnerFieldUnitary) :
    P1OffCharCoverThreeNoInner :=
  p1OffCharCoverThreeNoInner_of_cases hGA coverThreeNoInnerDiagLinear
    coverThreeNoInnerFieldLinear_holds coverThreeNoInnerDiagUnitary_of_certs hFU

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels) in
theorem p1OffCharCoverThreeNoInner_holds
    (hGA : GriessMultipliersAllModels) : P1OffCharCoverThreeNoInner :=
  p1OffCharCoverThreeNoInner_of_fieldUnitary hGA (coverThreeNoInnerFieldUnitary_holds hGA)

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
