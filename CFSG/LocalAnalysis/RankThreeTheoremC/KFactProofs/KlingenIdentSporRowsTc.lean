module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24ThreeChecks
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Certificate9417
public import Certificates.Certificate9418
public import Certificates.Certificate9419
public import Certificates.Certificate9500
public import Certificates.Certificate9501
public import Certificates.Certificate9502
public import Certificates.Certificate9503
public import Certificates.Certificate9504
public import Certificates.Certificate9505
public import Certificates.Certificate9506
public import Certificates.Certificate9507

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding CFSG.AGLEmbedding.R3

section McL3

open CFSG.AGLEmbedding.R3.McLThree


theorem genData_McL_three [Finite (NativeSporadic.Carrier .McL)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .McL) 3 :=
  genData_of_tc_cp (X := NativeSporadic.McL) (by norm_num)
    (tcGenDatum_of_check (spec3 21) (D := tcSpec) Nat.prime_three
      Certificates.certificate9417.1)
    (coverPointDatum_of_check (spec3 21) (D := cpSpec) Nat.prime_three
      Certificates.certificate9417.2.1 Certificates.certificate9417.2.2)

end McL3

section Suz3

open CFSG.AGLEmbedding.R3.SuzThree


theorem genData_Suz_three [Finite (NativeSporadic.Carrier .Suz)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .Suz) 3 :=
  genData_of_tc_cp (X := NativeSporadic.Suz) (by norm_num)
    (tcGenDatum_of_check (spec3 64) (D := tcSpec) Nat.prime_three
      Certificates.certificate9500.1)
    (coverPointDatum_of_check (spec3 64) (D := cpSpec) Nat.prime_three
      Certificates.certificate9500.2.1 Certificates.certificate9500.2.2)

end Suz3

section ON3

open CFSG.AGLEmbedding.R3.ONThree


theorem genData_ON_three [Finite (NativeSporadic.Carrier .ONan)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .ONan) 3 :=
  genData_of_tc_cp (X := NativeSporadic.ON) (by norm_num)
    (tcGenDatum_of_check (spec3 154) (D := tcSpec) Nat.prime_three
      Certificates.certificate9504.1)
    (coverPointDatum_of_check (spec3 154) (D := cpSpec) Nat.prime_three
      Certificates.certificate9504.2.1 Certificates.certificate9504.2.2)

end ON3

section Co13

open CFSG.AGLEmbedding.R3.Co1Three


theorem genData_Co1_three [Finite (NativeSporadic.Carrier .Co1)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .Co1) 3 :=
  genData_of_tc_cp (X := NativeSporadic.Co1) (by norm_num)
    (tcGenDatum_of_check (spec2 24) (D := tcSpec) Nat.prime_three
      Certificates.certificate9503.1)
    (coverPointDatum_of_check (spec2 24) (D := cpSpec) Nat.prime_three
      Certificates.certificate9503.2.1 Certificates.certificate9503.2.2)

end Co13

section Co23

open CFSG.AGLEmbedding.R3.Co2Three


theorem genData_Co2_three [Finite (NativeSporadic.Carrier .Co2)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .Co2) 3 :=
  genData_of_tc_cp (X := NativeSporadic.Co2) (by norm_num)
    (tcGenDatum_of_check (spec2 22) (D := tcSpec) Nat.prime_three
      Certificates.certificate9419.1)
    (coverPointDatum_of_check (spec2 22) (D := cpSpec) Nat.prime_three
      Certificates.certificate9419.2.1 Certificates.certificate9419.2.2)

end Co23

section Co33

open CFSG.AGLEmbedding.R3.Co3Three


theorem genData_Co3_three [Finite (NativeSporadic.Carrier .Co3)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .Co3) 3 :=
  genData_of_tc_cp (X := NativeSporadic.Co3) (by norm_num)
    (tcGenDatum_of_check (spec2 22) (D := tcSpec) Nat.prime_three
      Certificates.certificate9418.1)
    (coverPointDatum_of_check (spec2 22) (D := cpSpec) Nat.prime_three
      Certificates.certificate9418.2.1 Certificates.certificate9418.2.2)

end Co33

section Fi223

open CFSG.AGLEmbedding.R3.Fi22Three


theorem genData_Fi22_three [Finite (NativeSporadic.Carrier .Fi22)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .Fi22) 3 :=
  genData_of_tc_cp (X := NativeSporadic.Fi22) (by norm_num)
    (tcGenDatum_of_check (spec3 77) (D := tcSpec) Nat.prime_three
      Certificates.certificate9501.1)
    (coverPointDatum_of_check (spec3 77) (D := cpSpec) Nat.prime_three
      Certificates.certificate9501.2.1 Certificates.certificate9501.2.2)

end Fi223

section Fi233

open CFSG.AGLEmbedding.R3.Fi23Three


theorem genData_Fi23_three [Finite (NativeSporadic.Carrier .Fi23)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .Fi23) 3 :=
  genData_of_tc_cp (X := NativeSporadic.Fi23) (by norm_num)
    (tcGenDatum_of_check (spec3 253) (D := tcSpec) Nat.prime_three
      Certificates.certificate9507.1)
    (coverPointDatum_of_check (spec3 253) (D := cpSpec) Nat.prime_three
      Certificates.certificate9507.2.1 Certificates.certificate9507.2.2)

end Fi233

section HN3

open CFSG.AGLEmbedding.R3.HNThree


theorem genData_HN_three [Finite (NativeSporadic.Carrier .HN)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .HN) 3 :=
  genData_of_tc_cp (X := NativeSporadic.HN) (by norm_num)
    (tcGenDatum_of_check (specP 5 133) (D := tcSpec) Nat.prime_three
      Certificates.certificate9506.1)
    (coverPointDatum_of_check (specP 5 133) (D := cpSpec) Nat.prime_three
      Certificates.certificate9506.2.1 Certificates.certificate9506.2.2)

end HN3

section HN5

open CFSG.AGLEmbedding.R3.HNFive


theorem genData_HN_five [Finite (NativeSporadic.Carrier .HN)] [Fact (Nat.Prime 5)] :
    GenData (NativeSporadic.Carrier .HN) 5 :=
  genData_of_tc_cp (X := NativeSporadic.HN) (by norm_num)
    (tcGenDatum_of_check (specP 5 133) (D := tcSpec) Nat.prime_five
      Certificates.certificate9505.1)
    (coverPointDatum_of_check (specP 5 133) (D := cpSpec) Nat.prime_five
      Certificates.certificate9505.2.1 Certificates.certificate9505.2.2)

end HN5

section Co15

open CFSG.AGLEmbedding.R3.Co1Five


theorem genData_Co1_five [Finite (NativeSporadic.Carrier .Co1)] [Fact (Nat.Prime 5)] :
    GenData (NativeSporadic.Carrier .Co1) 5 :=
  genData_of_tc_cp (X := NativeSporadic.Co1) (by norm_num)
    (tcGenDatum_of_check (spec2 24) (D := tcSpec) Nat.prime_five
      Certificates.certificate9502.1)
    (coverPointDatum_of_check (spec2 24) (D := cpSpec) Nat.prime_five
      Certificates.certificate9502.2.1 Certificates.certificate9502.2.2)

end Co15

section Fi243

open CFSG.AGLEmbedding.R3.Fi24Three


theorem genData_Fi24_three [Finite (NativeSporadic.Carrier .Fi24Prime)] [Fact (Nat.Prime 3)] :
    GenData (NativeSporadic.Carrier .Fi24Prime) 3 :=
  genData_of_tc_cp (X := NativeSporadic.Fi24prime) (by norm_num)
    (tcGenDatum_of_check (CFSG.RankThree.Asc83Table.matOpsSpec 3 781) (D := tcSpec)
      Nat.prime_three tcCheck_Fi24)
    (coverPointDatum_of_check (CFSG.RankThree.Asc83Table.matOpsSpec 3 781) (D := cpSpec)
      Nat.prime_three cpCheck_Fi24 noFun_Fi24)

end Fi243

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
