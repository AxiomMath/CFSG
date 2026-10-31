module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.CGT.T75JM.M22PresInputs

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable CFSG.Blueprint CFSG.Sporadic.Mathieu

abbrev m22Presented : Type := PG 7 m22Rels

abbrev M22Facts : Prop :=
  (Finite m22Presented ∧ Nat.card m22Presented ≤ 443520) ∧ m22TabCheck = true

end CFSG.CGT.T75JM
