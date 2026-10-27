
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLatticeCoreBase

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLatticeAbs
public import CFSG.Sporadic.Schreier.TitsStabCheck
public import CFSG.Certificates.NativeInvariantMerge
public import CFSG.Sporadic.Schreier.TitsLocal
public import CFSG.Sporadic.Schreier.TitsPrim
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public import CFSG.Sporadic.Schreier.TitsStabCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public import Certificates.Certificate4139

public noncomputable section

namespace CFSG.QuasithinUnique.Setup.X6.TitsLat

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits

theorem tits_overgroups
    (M : Subgroup titsD) (hM : titsFlagStab ≤ M) :
    M = titsFlagStab ∨ M = titsPointStab ∨ M = titsLineStab ∨ M = ⊤ :=
  Certificates.certificate4139 M hM

end CFSG.QuasithinUnique.Setup.X6.TitsLat
