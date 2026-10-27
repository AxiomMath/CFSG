module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Data

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def tab6Row : Fin 8 → OrbRow :=
  ![tab6Row0, tab6Row1, tab6Row2, tab6Row3, tab6Row4, tab6Row5, tab6Row6, tab6Row7]

@[expose] def tab6Cap : ℕ := 100000

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
