module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclRed
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclF4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclSU5
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclU6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclTE6Lang
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclTE6D4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HStdExcl

theorem exclU6_holds :
    ExclU6 :=
  exclU6_of_su5Mult sU5Mult_holds

theorem stdCovDiagExclAt_of_exclTE6
    (hT : ExclTE6) : StdCovDiagExclAt :=
  stdCovDiagExclAt_of_quot exclF4_holds exclU6_holds hT

theorem stdCovDiagExclAt_of_d4
    (hD4 : E6TwoD4NotSmall) : StdCovDiagExclAt :=
  stdCovDiagExclAt_of_exclTE6 (exclTE6_of_rat (e6TwoRatNotSmall_of_d4 hD4))

theorem exclTE6_holds :
    ExclTE6 :=
  exclTE6_of_rat (e6TwoRatNotSmall_of_d4 e6TwoD4NotSmall_holds)

theorem stdCovDiagExclAt_holds :
    StdCovDiagExclAt :=
  stdCovDiagExclAt_of_d4 e6TwoD4NotSmall_holds

end CFSG.LocalAnalysis.GLTheoremA.HStdExcl

end
