module

public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate9584

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem co1_fusd2_check :
    fusCheck (ops2 24) NativeSporadic.Co1Seed1 NativeSporadic.Co1Seed2
      fusD2Co1N fusD2Co1Prog fusD2Co1 = true :=
  Certificates.certificate9584

theorem fusionGenerationOf_Co1_seven :
    FusionGenerationOf NativeSporadic.Co1 7 :=
  fusionGenerationOf_of_check (spec2 24) (D := fusD2Co1) Nat.prime_seven co1_fusd2_check

end CFSG.AGLEmbedding
