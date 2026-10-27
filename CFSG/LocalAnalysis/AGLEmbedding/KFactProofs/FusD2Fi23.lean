module

public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate9585

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.CTP.Fus CFSG.SectionRank
open CFSG.SectionRank.Native CFSG.Blueprint

theorem fi23_fusd2_check :
    fusCheck (ops3 253) NativeSporadic.Fi23Seed1 NativeSporadic.Fi23Seed2
      fusD2Fi23N fusD2Fi23Prog fusD2Fi23 = true :=
  Certificates.certificate9585

theorem fusionGenerationOf_Fi23_five :
    FusionGenerationOf NativeSporadic.Fi23 5 :=
  fusionGenerationOf_of_check (spec3 253) (D := fusD2Fi23) Nat.prime_five fi23_fusd2_check

end CFSG.AGLEmbedding
