module

public import CFSG.CGT.A8S.Main
public import CFSG.CGT.A8S.CoreTrivial3
public import CFSG.CGT.A8S.Pair
public import CFSG.CGT.A8S.N0Iso
public import CFSG.CGT.A8S.L2Main
public import CFSG.CGT.A8S.R3Main
public import CFSG.CGT.A8S.A8PresCert
public import CFSG.Holt.H78.Theorem1

public section

namespace CFSG.CGT.A8S

theorem a8SylowInput :
    CFSG.CGT.T75P.A8SylowInput :=
  a8SylowInput_of_parts (holtA9Statement_of_holt CFSG.Holt.H78.holtTheorem1)
    (coreStatementA8_of_holt CFSG.Holt.H78.holtTheorem1)
    (pairStatementA8_of_holt CFSG.Holt.H78.holtTheorem1) n0StatementA8 l2StatementA8_of_n0
    r3StatementA8 (r5StatementA8_of_card_le ⟨finite_pg_relsN0A8, card_pg_relsN0A8.le⟩)

end CFSG.CGT.A8S
