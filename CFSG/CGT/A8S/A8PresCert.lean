module

public import CFSG.CGT.A8S.A8Pres
public import CFSG.CGT.A8S.Interfaces
public import Certificates.Certificate21199

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable

theorem a8Enum_eq_true : A8SubIndex :=
  Certificates.certificate21199.1

theorem r5StatementA8_of_card_le
    (hN0 : Finite (PG 5 relsN0A8) ∧ Nat.card (PG 5 relsN0A8) ≤ 1344) : R5StatementA8 := by
  intro H _ e hp hK
  have := hN0.1
  exact exists_mulEquiv_A8_of_relations a8Enum_eq_true hN0.2 e hp hK

end CFSG.CGT.A8S
