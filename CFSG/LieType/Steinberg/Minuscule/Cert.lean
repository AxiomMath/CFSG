module

public import CFSG.LieType.Steinberg.Minuscule.CertInputs
public import Certificates.Certificate115

public import CFSG.Blueprint.ChevalleyStrings
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley

namespace MinData

variable {τ : Tag} (D : MinData τ)

end MinData

theorem e6Data_checkWeights : e6Data.checkWeights = true := by
  exact Certificates.certificate115.1

theorem e6Data_checkWeylTable : e6Data.checkWeylTable = true := by
  exact Certificates.certificate115.2.1

theorem e6Data_checkSimple : e6Data.checkSimple = true := by
  exact Certificates.certificate115.2.2.1

theorem e6Data_checkWeyl : e6Data.checkWeyl = true := by
  exact Certificates.certificate115.2.2.2.1

theorem e6Data_checkPairs : e6Data.checkPairs = true := by
  exact Certificates.certificate115.2.2.2.2.1

theorem e6Data_checkBraid : e6Data.checkBraid = true := by
  exact Certificates.certificate115.2.2.2.2.2.1

theorem e6Data_checkPGen : e6Data.checkPGen = true := by
  exact Certificates.certificate115.2.2.2.2.2.2.1

theorem e6Data_checkGrading : e6Data.checkGrading = true := by
  exact Certificates.certificate115.2.2.2.2.2.2.2.1

theorem e7Data_checkWeights : e7Data.checkWeights = true := by
  exact Certificates.certificate115.2.2.2.2.2.2.2.2.1

theorem e7Data_checkWeylTable : e7Data.checkWeylTable = true := by
  exact Certificates.certificate115.2.2.2.2.2.2.2.2.2.1

theorem e7Data_checkSimple : e7Data.checkSimple = true := by
  exact Certificates.certificate115.2.2.2.2.2.2.2.2.2.2.1

theorem e7Data_checkWeyl : e7Data.checkWeyl = true := by
  exact Certificates.certificate115.2.2.2.2.2.2.2.2.2.2.2.1

theorem e7Data_checkPairs : e7Data.checkPairs = true := by
  exact Certificates.certificate115.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e7Data_checkBraid : e7Data.checkBraid = true := by
  exact Certificates.certificate115.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e7Data_checkPGen : e7Data.checkPGen = true := by
  exact Certificates.certificate115.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e7Data_checkGrading : e7Data.checkGrading = true := by
  exact Certificates.certificate115.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem e6Data_check : e6Data.check = true := by
  simp only [MinData.check, e6Data_checkWeights, e6Data_checkWeylTable, e6Data_checkSimple,
    e6Data_checkWeyl, e6Data_checkPairs, e6Data_checkBraid, e6Data_checkPGen, e6Data_checkGrading,
    Bool.and_self]

theorem e7Data_check : e7Data.check = true := by
  simp only [MinData.check, e7Data_checkWeights, e7Data_checkWeylTable, e7Data_checkSimple,
    e7Data_checkWeyl, e7Data_checkPairs, e7Data_checkBraid, e7Data_checkPGen, e7Data_checkGrading,
    Bool.and_self]

end CFSG.LieType.Steinberg.Minuscule
