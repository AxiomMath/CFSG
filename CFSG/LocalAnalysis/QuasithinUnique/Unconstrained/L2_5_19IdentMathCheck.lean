module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathNoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathData
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathNoLayer
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathData
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathCheckInputs
public import Certificates.Certificate4149
public import CFSG.Sporadic.Schreier.M24Base
public meta import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.QuasithinUnique.Id2519.MathNoLayer

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

theorem m23_noLayer_check :
    noLayerOK 23 (toTabs m23E) (allTables m23CentQ1) = true :=
  Certificates.certificate4149.1

theorem m22o_noLayer_check :
    noLayerOK 22 (toTabs m22oE) (allTables m22OutCentQ2) = true :=
  Certificates.certificate4149.2.1

theorem m24_noLayer_check :
    noLayerOK 24 (toTabs m24E) (allTables m24CentQ2) = true :=
  Certificates.certificate4149.2.2

end CFSG.QuasithinUnique.Id2519.MathNoLayer
