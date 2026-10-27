module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2SwapCert

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

variable {n : ℕ}



theorem v3AE6Glue_of_cert (hI : V3AE6I n) (hR : AE6ModelAE8) (hFin : AE6EdgePairsFin)
    (hT : AE6ModelTri) : V3AE6Glue n :=
  v3AE6Glue_of_fin hI hR hFin ae6EdgeSwapMem_of_cert hT

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2
