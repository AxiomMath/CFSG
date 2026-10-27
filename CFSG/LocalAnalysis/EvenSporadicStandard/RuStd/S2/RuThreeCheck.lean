module

public import Certificates.Certificate24945
public import Certificates.Certificate24946
public import Certificates.Certificate24947
public import Certificates.Certificate24948

public noncomputable section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier

theorem ruThree_Q_check :
    linesOKG 3 27 13 4060 ruThreeQGens ruThreeKeys ruThreeQCert ruThreeLines = true ∧
      allLt ruThreeQGens.size
        (fun l => siftA 4060 ruThreeLevels ruThreeBaseArr 0 ruThreeQGens[l]!) = true ∧
      transOKG 13 4060 ruThreeTransporters ruThreeLines ruThreeRec ruThreeLevels
        ruThreeBaseArr = true ∧
      allLt 13 (fun j => (List.range 1).any fun i => ruThreeRec.getD j 0 == i) = true ∧
      ruThreeRec.getD 0 0 = 0 :=
  Certificates.certificate24945

theorem ruThree_case0_check :
    caseChainOK2P 4060 ruThreeArrs ruThreeBaseArr ruThreeWords (ruArr4060 0) (ruArr4060 1) =
        true ∧
      rawOrbitSizes 4060 ruThreeArrs ruThreeBaseArr = [4060, 2304, 650, 8, 3, 1, 1] ∧
      validA 4060 (ruArr4060 0) = true ∧ validA 4060 (ruArr4060 1) = true ∧
      centOKP 3 4060 ruThreeArrs ruThreeBaseArr ruThreeLines[0]! ruThreeRels ruThreeC0Gens
        ruThreeKeys ruThreeC0Cert 2160 = true ∧
      eqA 4060 ruThreeC0Gens[0]! ruThreeLines[0]! = true ∧
      ruThreeInvOK = true :=
  Certificates.certificate24946

theorem ruThree_graph_check :
    prodOK 4060 11 ruThreeC0Gens ruThreeM ruThreeKeys ruThreeGraphCert = true ∧
      ruThreeGraphCert.pts.size = 2160 ∧ ruThreeKernelOK = true ∧
      eqA 11 ruThreeM[0]! (idA 11) = true :=
  Certificates.certificate24947

theorem ruThree_M10_check :
    enumOK 11 ruThreeM11 ruThreeKeys11 ruThreeM11Cert = true ∧
      enumOK 11 ruThreeM ruThreeKeys11 ruThreeTCert = true ∧
      ruThreeStabOK = true ∧ ruThreeStabCoverOK = true ∧ ruThreeCenterOK = true ∧
      oddNormalOK 11 ruThreeTCert = true :=
  Certificates.certificate24948

end CFSG.EvenSporadicStandard.RuStd.S2
