module

public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section BarM

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_barM {M X : Subgroup G} {p : ℕ} (hX : IsElemAbelian p X) :
    IsElemAbelian p (barM M X) :=
  isElemAbelian_barM_of_isElemAbelian hX

end BarM

end CFSG.AGLEmbedding
