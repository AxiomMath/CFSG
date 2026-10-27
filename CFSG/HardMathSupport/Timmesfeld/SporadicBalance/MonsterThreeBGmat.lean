module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveLift
public import Certificates.Certificate136220
public import Certificates.Certificate136221
public import Certificates.Certificate136222
public import Certificates.Certificate136223
public import Certificates.Certificate136224

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive

theorem m3bEqs_all :
    agreeAll m3bEqs = true := by
  have t3 : agreeAll (m3bEqs.drop 43) = true := Certificates.certificate136223
  have t2 : agreeAll (m3bEqs.drop 26) = true :=
    agreeAll_drop_split m3bEqs 26 17 (Certificates.certificate136222) t3
  have t1 : agreeAll (m3bEqs.drop 8) = true :=
    agreeAll_drop_split m3bEqs 8 18 (Certificates.certificate136221) t2
  have t0 : agreeAll (m3bEqs.drop 0) = true :=
    agreeAll_drop_split m3bEqs 0 8 (Certificates.certificate136220) t1
  simpa using t0

theorem m3bMoves_all :
    m3bMoves.all (fun w => EdgeNoncomm.moveCheck w (aV ())) = true :=
  Certificates.certificate136224

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
