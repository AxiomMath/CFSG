module

import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVZCore
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCoreToral
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltSplit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem barM_R (hc : D1IbConfig p P M H R Rbar K z) :
    IsElemAbelian p (barM M R) ∧ Nat.card (barM M R) = p ^ 3 :=
  hc.toZCore.barM_R

theorem false_of_le_rPart (hc : D1IbConfig p P M H R Rbar K z) (hB : D1IbBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hR : R ≤ rPart M R (barM M L)) :
    False := by
  obtain ⟨hEel, hEcard⟩ := hc.barM_R
  exact hc.toIbCore.false_of_le_rPart_of_elem hB hL hR le_rfl hEel hEcard

end D1IbConfig

end CFSG.AGLEmbedding
