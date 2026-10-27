module

public import CFSG.CGT.L5R.L52Pres
public import CFSG.CGT.L5R.Interfaces
public import CFSG.CGT.M24R.N8Cert
public import Certificates.Certificate21195

public section

namespace CFSG.CGT.L5R

open CFSG.CosetTable CFSG.CGT.M24R CFSG.GroupTheory.GL52

theorem l52Enum_eq_true : l52Enum = true :=
  Certificates.certificate21195

theorem r5Statement :
    R5Statement := by
  intro H _ e hp hK
  have := finite_pg_relsN8Ten
  exact exists_mulEquiv_G52_of_relations l52Enum_eq_true card_pg_relsN8Ten_le e hp hK

end CFSG.CGT.L5R
