module

public import Certificates.Data.CFSGNative.Ru.Data
public import Certificates.Data.CFSGNative.Th.Tables
public import Certificates.Data.CFSGNative.SporLat.BuildPt
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public meta import Certificates.Data.CFSGNative.Ru.Data
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.SporLat.BuildPt
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuCertificateInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuDcInputs
public import Certificates.Certificate4034
public import Certificates.Certificate3172
public import Certificates.Certificate4143

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.RuCert

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)

theorem ru_lat_cert :
    MembersOK ptAct ruData.n ruTaL ruTbL ruDelta ruLatK ∧ O2OK ptAct ruLatK ruOtK ∧
      (∀ j < 5, ∀ jj < 5, (GensIn ptAct ruDelta ruLatK j jj ↔ jj ∈ ruIncl[j]!)) ∧
      (∀ g : J ruData, lab ruData.n ptLab ruDelta g = ruDelta ↔
        g ∈ Subgroup.closure {x | x ∈ ruSgK}) ∧
      ∀ Z : Subgroup (J ruData), Subgroup.closure {x | x ∈ ruSgK} ≤ Z → ∃ j ≤ 5,
        Z = memberOrTop 5 (fun j => Subgroup.closure {x | x ∈ ruSgK ++
          (ruMw[j]!).map (wordElt (a ruData) (b ruData))}) j :=
  Certificates.certificate4034

end CFSG.QuasithinUnique.Ch1.SporLat.RuCert
