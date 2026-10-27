module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.MS93.SkConcl

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G]

@[expose] def MS93AS_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (M T L : Subgroup G), PUHyp M T L → MS93ConclAS M T L

end CFSG.Quasithin.MS93
