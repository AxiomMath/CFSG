module

public import CFSG.Fischer.UnitaryAction
public meta import Certificates.Data.CFSGNative.F4.Unitary
public import Certificates.Certificate1003
public import Mathlib

public section

namespace CFSG.Fischer

open CFSG.F4.Native

theorem upts_ok : uPtsOK = true :=
  Certificates.certificate1003

theorem ptsFacts : PtsFacts := ptsFacts_of upts_ok

end CFSG.Fischer
