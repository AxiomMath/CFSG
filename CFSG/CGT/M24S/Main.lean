module

public import CFSG.CGT.L5R.CaseLParts
public import CFSG.CGT.L5R.L2CertL
public import CFSG.CGT.L5R.R3
public import CFSG.CGT.L5R.L52PresCert

public section

namespace CFSG.CGT.M24S

theorem caseLInput :
    CaseLInput :=
  CFSG.CGT.L5R.caseLInput_of_parts CFSG.CGT.L5R.n8StatementL CFSG.CGT.L5R.l2StatementL_of_n8
    CFSG.CGT.L5R.r3StatementL CFSG.CGT.L5R.r5Statement CFSG.Holt.H78.holtTheorem1

theorem m24SylowInput :
    CFSG.CGT.T75P.M24SylowInput :=
  m24SylowInput_of_caseL caseLInput

end CFSG.CGT.M24S
