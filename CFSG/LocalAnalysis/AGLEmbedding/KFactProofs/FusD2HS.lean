module

public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate9583

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem hs_fusd2_check :
    fusCheck (ops2 20) NativeSporadic.HSSeed1 NativeSporadic.HSSeed2
      fusD2HSN fusD2HSProg fusD2HS = true :=
  Certificates.certificate9583

theorem fusionGenerationOf_HS_three :
    FusionGenerationOf NativeSporadic.HS 3 :=
  fusionGenerationOf_of_check (spec2 20) (D := fusD2HS) Nat.prime_three hs_fusd2_check

end CFSG.AGLEmbedding
