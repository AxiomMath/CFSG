module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutElemRankCatalog
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutElemRankAut

public section

namespace CFSG.AGLEmbedding

open CFSG.Open


theorem kFactOutElemRankOdd : KFactOutElemRankOdd := by
  intro Y _ _ L E hL hcat p hp hp2 hpL hEN hE hEC
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have : Group.IsPerfect ↥L := OutElemRank.isPerfect_of_quasisimple hq
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  exact OutElemRank.card_le_of_elementaryRankAtMostOne
    (OutElemRank.elementaryRankAtMostOne_of_catalogGroup
      (OutElemRank.exists_noncomm_of_quasisimple hq) hcat hp hp2
      (OutElemRank.not_dvd_card_quotient_center hpL)) hEN hE hEC

end CFSG.AGLEmbedding
