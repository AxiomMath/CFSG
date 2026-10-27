module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XAsm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA

section Certs


theorem i117At_of_autNorm
    (h : D4XF.D4TwoAutNormInn) (G : Type) [Group G] [Finite G] : I117At G :=
  i117At_of_d4Facts (D4XF.d4TwoFactsAt_of_residual h) G

theorem noTrialityAt_of_autNorm
    (h : D4XF.D4TwoAutNormInn) {G : Type} [Group G] [Finite G]
    (hbig : NoTrialityBigAt G) : FP.NoTrialityAt G :=
  noTrialityAt_of_d4Facts (D4XF.d4TwoFactsAt_of_residual h) hbig

end Certs

end CFSG.LocalAnalysis.GLTheoremA.D4T
