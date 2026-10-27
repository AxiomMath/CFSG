module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankLySound
public import Certificates.Certificate9605

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaLyRank

theorem rankLiftDatum_Ly_five :
    RankLiftDatum NativeSporadic.Ly 5 :=
  rankLiftDatum_of_ly5check (D := lyrlSpec) (tabs := lyrlTabs) Nat.prime_five
    Certificates.certificate9605

end CFSG.AGLEmbedding
