module

public import CFSG.Sporadic.SmallOddCore.McLLocalCheck
public meta import CFSG.Sporadic.SmallOddCore.McLLocalCheck
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLCheckInputs
public import Certificates.Certificate2024

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG.Sporadic.SmallOddCore CFSG.PSL3Four.Native

theorem mclX_order_six_check :
    wordTabS 35 mclXGens (List.replicate 6 mclSixWord).flatten = idTab 35 ∧
      ∀ k ∈ [1, 2, 3, 4, 5],
        (wordTabS 35 mclXGens (List.replicate k mclSixWord).flatten == idTab 35) = false :=
  Certificates.certificate2024

end CFSG.ComponentClassification.RestrictedStd.Spor
