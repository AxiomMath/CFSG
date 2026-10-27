module

public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9586

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem fi24prime_fusd2_check :
    fusCheck (ops3 781) NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2
      fusD2Fi24N fusD2Fi24Prog fusD2Fi24 = true :=
  Certificates.certificate9586

theorem fusionGenerationOf_Fi24prime_five :
    FusionGenerationOf NativeSporadic.Fi24prime 5 :=
  fusionGenerationOf_of_check (spec3 781) (D := fusD2Fi24) Nat.prime_five fi24prime_fusd2_check

end CFSG.AGLEmbedding
