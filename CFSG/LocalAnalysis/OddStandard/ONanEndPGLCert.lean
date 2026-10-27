module

public import CFSG.LocalAnalysis.OddStandard.ONanEndPGL
public import Certificates.Certificate6144

public section

namespace CFSG.OddStandard.ONanRec

open CFSG.GH74.KGroups.L34 CFSG.Blueprint F2

theorem pglCheck_cert : pglCheck = true :=
  Certificates.certificate6144

theorem eq_top_of_not_isConj_order_four_cert
    {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 2 X = ⊥) {K : Subgroup X} (hK : K.Normal)
    (hL : LieModel K .PSL 3 2 2) (hidx : K.index ∣ 3) {u v : X} (hu : orderOf u = 4)
    (hv : orderOf v = 4) (hnc : ¬ IsConj u v) : K = ⊤ :=
  eq_top_of_not_isConj_order_four pglCheck_cert hO hK hL hidx hu hv hnc

end CFSG.OddStandard.ONanRec
