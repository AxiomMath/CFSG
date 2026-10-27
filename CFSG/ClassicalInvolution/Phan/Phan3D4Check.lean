module

public import CFSG.ClassicalInvolution.Phan.Phan3D4Defs
public import CFSG.Certificates.CosetTableCompactColumns
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def sl3OrderCheck : Bool := subsetCheckCC sl3Rels [] 100000 5616

end CFSG.ClassicalInvolution.Phan.Q3G
