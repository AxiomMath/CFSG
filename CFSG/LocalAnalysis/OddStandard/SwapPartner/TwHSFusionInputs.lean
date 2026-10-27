module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterCheckInputs

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Th.Native CFSG.QuasithinUnique.Id2519.HSAut

@[expose] def fusUTab : Tab := natArr (hsCentTbl 21)

@[expose] def fusB0Tab : Tab :=
  comp 3850 (comp 3850 e2Tab e1Tab) (comp 3850 (comp 3850 e2Tab e1Tab) (comp 3850 e2Tab e1Tab))

@[expose] def fusFix (t : Tab) : Nat := countBelow 3850 fun i => t[i]! == i

@[expose] def fusOrbit : Enum := orbitBFS 3850 gensE ginvE fusB0Tab 300

@[expose] def fusionCheck : Bool :=
  (hsCentTbl 21).size == 3850 && CFSG.Sporadic.SmallOddCore.permOK 3850 (hsCentTbl 21) &&
    comp 3850 fusB0Tab fusB0Tab == idTab 3850 &&
    orbitOK 3850 gensE ginvE fusB0Tab fusOrbit && fusOrbit.tabs.size == 210 &&
    fusFix (comp 3850 fusUTab fusB0Tab) != fusFix fusUTab

end CFSG.OddStandard.AltStdSec.SwapPartner
