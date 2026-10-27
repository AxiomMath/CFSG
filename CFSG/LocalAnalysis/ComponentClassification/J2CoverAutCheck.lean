
module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Certificate10019
public import Certificates.Data.CFSGNative.J2.Certificate
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public meta import Certificates.Data.CFSGNative.J2.Certificate
public import Certificates.Certificate10019Base

public section

namespace CFSG.ComponentClassification.J2Cover

open CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native

theorem autChain_check :
    rawChainOK 315 (autStrong.extract 0 2) autStrong autBase autWords 4 = true ∧
      rawOrbitSizes 315 autStrong autBase = [315, 160, 12] :=
  Certificates.certificate10019.1

theorem orb_check :
    allLt 315 (fun i => ap (CFSG.Sporadic.J2.Native.orbitData ()).alpha i == autStrong[0]![i]! &&
      ap (CFSG.Sporadic.J2.Native.orbitData ()).beta i == autStrong[1]![i]!) = true :=
  Certificates.certificate10019.2.1

theorem pair_check :
    ordTest 315 2 tblA = true ∧ ordTest 315 3 tblB = true ∧
      pairTest 315 7 12 2 3 tblA tblB = true ∧
      (orderTablesOf (idT 315) 2).length = 2835 ∧ (orderTablesOf (idT 315) 3).length = 17360 ∧
      classOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2) 4000 = true ∧
      classTotal 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2)
        (orderTablesOf (idT 315) 3) 4000 7 12 2 3 = 1209600 :=
  Certificates.certificate10019.2.2.1

theorem outer_check :
    inP outerArr = false ∧ inP (compA 315 outerArr (compA 315 autStrong[0]! outerArr)) = true ∧
      inP (compA 315 outerArr (compA 315 autStrong[1]! outerArr)) = true :=
  Certificates.certificate10019.2.2.2.1

theorem classes_check :
    inP twoAArr = true ∧
      repsOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2) [tblA, tblTwoA]
        4000 = true ∧
      repSizes 315 #[tblA, tblB] #[tblAInv, tblBInv] [tblA, tblTwoA] 4000 = [2520, 315] ∧
      repsOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf tblU 2) [tblU] 4000 = true ∧
      repSizes 315 #[tblA, tblB] #[tblAInv, tblBInv] [tblU] 4000 = [1800] :=
  Certificates.certificate10019.2.2.2.2.1

theorem cent2B_check :
    rawChainOK 315 (cent2BStrong.extract 0 2) cent2BStrong cent2BBase cent2BWords 4 = true ∧
      rawOrbitSizes 315 cent2BStrong cent2BBase = [60, 4] ∧
      inP cent2BStrong[0]! = true ∧ inP cent2BStrong[1]! = true ∧
      commA cent2BStrong[0]! autStrong[0]! = true ∧ commA cent2BStrong[1]! autStrong[0]! = true ∧
      oddWitnessOK 315 15
        (filterProducts 315 allTrue (chainTables 315 cent2BStrong cent2BBase) (idT 315) []) =
        true :=
  Certificates.certificate10019.2.2.2.2.2.1

theorem cent2A_check :
    rawChainOK 315 (cent2AStrong.extract 0 2) cent2AStrong cent2ABase cent2AWords 4 = true ∧
      rawOrbitSizes 315 cent2AStrong cent2ABase = [160, 4, 3] ∧
      inP cent2AStrong[0]! = true ∧ inP cent2AStrong[1]! = true ∧
      commA cent2AStrong[0]! twoAArr = true ∧ commA cent2AStrong[1]! twoAArr = true ∧
      oddWitnessOK 315 15
        (filterProducts 315 allTrue (chainTables 315 cent2AStrong cent2ABase) (idT 315) []) =
        true :=
  Certificates.certificate10019.2.2.2.2.2.2.1

theorem centOuter_check :
    rawChainOK 315 (centOuterStrong.extract 0 2) centOuterStrong centOuterBase centOuterWords 4 =
        true ∧
      rawOrbitSizes 315 centOuterStrong centOuterBase = [42, 8] ∧
      inP centOuterStrong[0]! = true ∧ inP centOuterStrong[1]! = true ∧
      commA centOuterStrong[0]! outerArr = true ∧ commA centOuterStrong[1]! outerArr = true ∧
      oddWitnessOK 315 21
        (filterProducts 315 allTrue (chainTables 315 centOuterStrong centOuterBase) (idT 315) []) =
        true :=
  Certificates.certificate10019.2.2.2.2.2.2.2.1

theorem sylow_check :
    rawChainOK 315 (sylowStrong.extract 0 3) sylowStrong sylowBase sylowWords 4 = true ∧
      rawOrbitSizes 315 sylowStrong sylowBase = [64, 4] ∧
      inP (compA 315 sylowStrong[0]! outerArr) = true ∧
      inP (compA 315 sylowStrong[1]! outerArr) = true ∧
      inP (compA 315 sylowStrong[2]! outerArr) = true :=
  Certificates.certificate10019.2.2.2.2.2.2.2.2

end CFSG.ComponentClassification.J2Cover
