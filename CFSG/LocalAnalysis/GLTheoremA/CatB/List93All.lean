module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Id23
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2b
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93RkL2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93RkTits
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93RkSz

public section

namespace CFSG.LocalAnalysis.GLTheoremA.List93

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem i9List93Residual_holds : I9List93Residual :=
  ⟨chevOdd_holds, chev23_holds, l2Two_holds, tits_holds, suzuki_holds, notChev2_holds⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.List93
