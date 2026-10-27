module

public import CFSG.CGT.L5R.R3Main
public import Certificates.Certificate21197

public section

namespace CFSG.CGT.L5R

theorem r3FactsL_of_certificate : R3.R3FactsL :=
  ⟨Certificates.certificate21197.1, Certificates.certificate21197.2⟩

theorem r3StatementL :
    R3StatementL :=
  R3.r3StatementL_of_facts r3FactsL_of_certificate

end CFSG.CGT.L5R
