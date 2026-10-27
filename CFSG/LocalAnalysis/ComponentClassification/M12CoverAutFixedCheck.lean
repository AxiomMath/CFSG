module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData
public import Certificates.Certificate10024
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Certificates CFSG.Sporadic.Schreier

set_option compiler.extract_closed false

theorem checkChainD_eq : checkChainD = true :=
  Certificates.certificate10024.1

theorem checkFour_eq : checkFour (enumeration fixedDQ) = true :=
  Certificates.certificate10024.2.1

theorem checkInvolutions_eq :
    checkInvolutions (enumeration fixedDQ) = true :=
  Certificates.certificate10024.2.2.1

theorem checkConj_eq : checkConj (enumeration fixedDQ) = true :=
  Certificates.certificate10024.2.2.2.1

theorem checkKernel_eq : checkKernel (enumeration fixedDQ) = true :=
  Certificates.certificate10024.2.2.2.2.1

theorem checkPairs_eq : checkPairs (enumeration fixedDQ) = true :=
  Certificates.certificate10024.2.2.2.2.2.1

theorem checkCount_eq : checkCount (enumeration fixedDQ) = true :=
  Certificates.certificate10024.2.2.2.2.2.2.1

theorem checkFourMul_eq : checkFourMul = true :=
  Certificates.certificate10024.2.2.2.2.2.2.2.1

theorem checkFourInv_eq : checkFourInv = true :=
  Certificates.certificate10024.2.2.2.2.2.2.2.2.1

theorem checkFourAbelian_eq : checkFourAbelian = true :=
  Certificates.certificate10024.2.2.2.2.2.2.2.2.2.1

theorem checkFourDistinctEntries_eq :
    checkFourDistinctEntries = true :=
  Certificates.certificate10024.2.2.2.2.2.2.2.2.2.2.1

theorem checkFourSeparated_eq : checkFourSeparated = true :=
  Certificates.certificate10024.2.2.2.2.2.2.2.2.2.2.2.1

theorem checkFourArrays_eq : checkFourArrays = true :=
  Certificates.certificate10024.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem checkFourWords_eq : checkFourWords = true :=
  Certificates.certificate10024.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem checkFourIndex_eq : checkFourIndex = true :=
  Certificates.certificate10024.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.ComponentClassification.M12Cover
