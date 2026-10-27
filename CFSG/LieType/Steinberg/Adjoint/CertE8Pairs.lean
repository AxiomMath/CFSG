module

public import Certificates.Certificate80

public import CFSG.LieType.Steinberg.Adjoint.Cert
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.LieType.Steinberg.Adjoint

theorem e8Data_checkPairs_0 : e8Data.checkPairsRange 0 20 = true := by
  exact Certificates.certificate80.1

theorem e8Data_checkPairs_1 : e8Data.checkPairsRange 20 20 = true := by
  exact Certificates.certificate80.2.1

theorem e8Data_checkPairs_2 : e8Data.checkPairsRange 40 20 = true := by
  exact Certificates.certificate80.2.2.1

theorem e8Data_checkPairs_3 : e8Data.checkPairsRange 60 20 = true := by
  exact Certificates.certificate80.2.2.2.1

theorem e8Data_checkPairs_4 : e8Data.checkPairsRange 80 20 = true := by
  exact Certificates.certificate80.2.2.2.2.1

theorem e8Data_checkPairs_5 : e8Data.checkPairsRange 100 20 = true := by
  exact Certificates.certificate80.2.2.2.2.2.1

theorem e8Data_checkPairs_6 : e8Data.checkPairsRange 120 20 = true := by
  exact Certificates.certificate80.2.2.2.2.2.2.1

theorem e8Data_checkPairs_7 : e8Data.checkPairsRange 140 20 = true := by
  exact Certificates.certificate80.2.2.2.2.2.2.2.1

theorem e8Data_checkPairs_8 : e8Data.checkPairsRange 160 20 = true := by
  exact Certificates.certificate80.2.2.2.2.2.2.2.2.1

theorem e8Data_checkPairs_9 : e8Data.checkPairsRange 180 20 = true := by
  exact Certificates.certificate80.2.2.2.2.2.2.2.2.2.1

theorem e8Data_checkPairs_10 : e8Data.checkPairsRange 200 20 = true := by
  exact Certificates.certificate80.2.2.2.2.2.2.2.2.2.2.1

theorem e8Data_checkPairs_11 : e8Data.checkPairsRange 220 20 = true := by
  exact Certificates.certificate80.2.2.2.2.2.2.2.2.2.2.2

end CFSG.LieType.Steinberg.Adjoint
