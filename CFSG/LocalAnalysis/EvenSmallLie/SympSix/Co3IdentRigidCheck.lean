
module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidCheckBase

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCube
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCube
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidCheckInputs
public import Certificates.Certificate3096

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native

theorem e3_check : e3Check = true :=
  Certificates.certificate3096

end CFSG.EvenSmallLie.SympSix.Co3Ident
