module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XNMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TNoTri
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank23

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA

section Certs


theorem i117At_of_d4Facts
    (hF : D4TwoFactsAt) (G : Type) [Group G] [Finite G] : I117At G :=
  i117At_of_facts (CatB.rank23At_holds G) hF (d4TwoNormalizes_holds G)

theorem noTrialityAt_of_d4Facts
    (hF : D4TwoFactsAt) {G : Type} [Group G] [Finite G]
    (hbig : NoTrialityBigAt G) : FP.NoTrialityAt G :=
  noTrialityAt_of_split (i117At_of_d4Facts hF G) (d4TwoNormalizes_holds G) hbig

end Certs

end CFSG.LocalAnalysis.GLTheoremA.D4T
