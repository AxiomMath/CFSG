module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZC
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Bridge.M23Surj
public import Certificates.Certificate42301

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint

theorem zcw_M22_5 : ZCW ↥NativeSporadic.M22 5 :=
  Certificates.certificate42301.1

theorem zcw_M22_7 : ZCW ↥NativeSporadic.M22 7 :=
  Certificates.certificate42301.2.1

theorem zcw_M23_5 : ZCW ↥NativeSporadic.M23 5 :=
  Certificates.certificate42301.2.2

theorem row_M22_5 :
    KFactSporLocalRow .M22 5 :=
  row_of_zcw CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    (by rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num) zcw_M22_5 (by decide)

theorem row_M22_7 :
    KFactSporLocalRow .M22 7 :=
  row_of_zcw CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    (by rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num) zcw_M22_7 (by decide)

theorem row_M23_5 :
    KFactSporLocalRow .M23 5 :=
  row_of_zcw CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
    (by rw [CFSG.Sporadic.Schreier.m23_card]; norm_num) zcw_M23_5 (by decide)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
