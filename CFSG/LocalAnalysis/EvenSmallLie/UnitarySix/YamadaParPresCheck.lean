module

public import Certificates.Certificate3301

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem uPres_card :
    Finite (CFSG.CosetTable.PG 5 uWS) ∧ Nat.card (CFSG.CosetTable.PG 5 uWS) ≤ 51840 :=
  Certificates.certificate3301.1

theorem uRelCheck_eq_true : uRelCheck = true :=
  Certificates.certificate3301.2.1

theorem uGenCheck_eq_true : uGenCheck = true :=
  Certificates.certificate3301.2.2

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
