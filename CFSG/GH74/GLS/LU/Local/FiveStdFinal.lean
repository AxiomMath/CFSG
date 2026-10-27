module

public import CFSG.GH74.GLS.LU.Local.FiveStdLeaf
public import Certificates.Certificate5147

public section

namespace CFSG.GH74.GLS.LU.Local.Five

theorem fiveModelLeaves_of_check : FiveModelBaseLeaf ∧ FiveModelLeaf :=
  ⟨fiveModelBaseLeaf_of_check Certificates.certificate5147,
    fiveModelLeaf_of_check Certificates.certificate5147⟩

end CFSG.GH74.GLS.LU.Local.Five
