module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveLift
public import Certificates.Certificate13699
public import Certificates.Certificate136100
public import Certificates.Certificate136101
public import Certificates.Certificate136102
public import Certificates.Certificate136103
public import Certificates.Certificate136104
public import Certificates.Certificate136105
public import Certificates.Certificate136106
public import Certificates.Certificate136107
public import Certificates.Certificate136108
public import Certificates.Certificate136109
public import Certificates.Certificate136110
public import Certificates.Certificate136111

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

theorem relEqs_all :
    agreeAll relEqs = true := by
  have t7 : agreeAll (relEqs.drop 68) = true := Certificates.certificate136106
  have t6 : agreeAll (relEqs.drop 57) = true :=
    agreeAll_drop_split relEqs 57 11 (Certificates.certificate136105) t7
  have t5 : agreeAll (relEqs.drop 47) = true :=
    agreeAll_drop_split relEqs 47 10 (Certificates.certificate136104) t6
  have t4 : agreeAll (relEqs.drop 41) = true :=
    agreeAll_drop_split relEqs 41 6 (Certificates.certificate136103) t5
  have t3 : agreeAll (relEqs.drop 35) = true :=
    agreeAll_drop_split relEqs 35 6 (Certificates.certificate136102) t4
  have t2 : agreeAll (relEqs.drop 25) = true :=
    agreeAll_drop_split relEqs 25 10 (Certificates.certificate136101) t3
  have t1 : agreeAll (relEqs.drop 13) = true :=
    agreeAll_drop_split relEqs 13 12 (Certificates.certificate136100) t2
  have t0 : agreeAll (relEqs.drop 0) = true :=
    agreeAll_drop_split relEqs 0 13 (Certificates.certificate13699) t1
  simpa using t0

theorem normEqs_all :
    agreeAll normEqs = true := by
  have t4 : agreeAll (normEqs.drop 23) = true := Certificates.certificate136111
  have t3 : agreeAll (normEqs.drop 17) = true :=
    agreeAll_drop_split normEqs 17 6 (Certificates.certificate136110) t4
  have t2 : agreeAll (normEqs.drop 11) = true :=
    agreeAll_drop_split normEqs 11 6 (Certificates.certificate136109) t3
  have t1 : agreeAll (normEqs.drop 5) = true :=
    agreeAll_drop_split normEqs 5 6 (Certificates.certificate136108) t2
  have t0 : agreeAll (normEqs.drop 0) = true :=
    agreeAll_drop_split normEqs 0 5 (Certificates.certificate136107) t1
  simpa using t0

theorem fiveRels_holds :
    ∀ r ∈ relSet 5 (pwF 9 fivePw) (cwF 9 fiveCw),
      FreeGroup.lift (fun i : Fin 9 => gw fiveGens[i.val]!) r = 1 :=
  fiveRels relEqs_all

theorem fiveNorm_holds :
    ∀ j < 3, ∀ i < 9, gw fiveNW[j]! * gw fiveGens[i]! * (gw fiveNW[j]!)⁻¹ =
      FreeGroup.lift (fun i : Fin 9 => gw fiveGens[i.val]!) (wordF 9 (fiveNImg[j]!)[i]!) :=
  fiveNorm (powEqs_of_relEqs relEqs_all) normEqs_all

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
