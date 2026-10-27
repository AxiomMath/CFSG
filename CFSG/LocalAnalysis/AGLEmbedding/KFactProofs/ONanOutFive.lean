module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutFiveCatalog
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutElemRankAut

public section

namespace CFSG.AGLEmbedding

open CFSG.Open


theorem kFactOutFiveCyclicDvd : KFactOutFiveCyclicDvd := by
  intro Y _ _ L E Q hL hcat _ hEN hE hcard hdisj hQL hQE hirr
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have : Group.IsPerfect ↥L := OutElemRank.isPerfect_of_quasisimple hq
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  exact OutFive.false_of_outPlaneSeries
    (OutFive.outPlaneSeries_of_catalogGroup (OutElemRank.exists_noncomm_of_quasisimple hq) hcat
      Nat.prime_five (by norm_num)) hEN hE hcard hdisj hQL hQE hirr

end CFSG.AGLEmbedding
