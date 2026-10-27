module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K155XMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA

structure I155XRes : Prop where
  n : K155X.L154NonInnDiag
  t : K155X.L154NotTD4

theorem i155XAt_of_res (h : I155XRes) (G : Type) [Group G] [Finite G] (p : ℕ) : I155X.I155XAt G p :=
  K155X.i155XAt_of_facts h.n h.t G p

end CFSG.LocalAnalysis.GLTheoremA
