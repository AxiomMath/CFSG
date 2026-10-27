module

public import CFSG.LocalAnalysis.Gross82.OrderThreeE6
public import CFSG.LocalAnalysis.Gross82.OrderThreeTwistedE6
import CFSG.LocalAnalysis.Gross82.OrderThreeResidual

public section

namespace CFSG.LocalAnalysis.Gross82

section Core



theorem r891GrossCoreOrderThree_holds : R891GrossCoreOrderThree :=
  r891GrossCoreOrderThree_of_E6
    (fun K _ _ n ℓ f hadm hmodel h3 _ _ _ => grossThreeInnerOrderThree_E6
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hadm hmodel h3)
    (fun K _ _ n ℓ f hadm hmodel h3 _ _ _ => grossThreeInnerOrderThree_twistedE6
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hadm hmodel h3)

end Core

end CFSG.LocalAnalysis.Gross82
