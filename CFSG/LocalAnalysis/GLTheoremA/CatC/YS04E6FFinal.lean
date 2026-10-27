module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6F
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04BCHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04LU
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D4FFinal

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem ys04_of_I117
    (hI : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → I117D4UsedAt G) : YS04 :=
  ys04_holds_of_bcRes hI YS04LU.kd26bcLinUni_holds kd26bcD4_holds kd26fE6_holds

end Certs

end CFSG.LocalAnalysis.GLTheoremA
