module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneAsm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenOuter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenAssembly
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenE6Three

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

section Exc


theorem genPlaneCompOn_exc_holds : GenPlaneCompOn S2019.S2019ExcCoreIdx :=
  genPlaneExcAssembly_holds genNormalExcInner_holds genNormalExcOuter_holds genPlaneE6Three_holds

section All


theorem s267FactGen_of_cls
    (hc : GenPlaneCompOn S267ClassicalIdx) : S267FactGen :=
  s267FactGen_of_planes hc genPlaneCompOn_exc_holds

end All

end Exc

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
