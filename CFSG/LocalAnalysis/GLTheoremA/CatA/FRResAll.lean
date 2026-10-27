module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRRes168
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTD4
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat13

public section

namespace CFSG.LocalAnalysis.GLTheoremA


theorem ys09FRTables_holds : YS09FRTables where
  small := FR.Res.smallDatum_holds
  twF4 := fun _ hp hp2 => FR.Res.twF4Core_holds hp hp2
  td4 := FR.Res.td4Core_holds
  r168 := fun R _ hs hc => FR.hR168 R hs hc

namespace FR

variable {G : Type} [Group G] [Finite G]

theorem i91CentIAt_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : I91CentIAt G p :=
  i91CentIAt_of_residuals hp hp2 Res.smallDatum_holds (Res.twF4Core_holds hp hp2) Res.td4Core_holds

theorem i91CompAt_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : I91CompAt G p :=
  i91CompAt_of_residuals hp hp2 Res.smallDatum_holds (Res.twF4Core_holds hp hp2) Res.td4Core_holds
    fun R _ hs hc => hR168 R hs hc

end FR

end CFSG.LocalAnalysis.GLTheoremA
