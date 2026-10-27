module

public import CFSG.CGT.A8S.RelData
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CGT.A8S.N0

open CFSG.CosetTable

abbrev l3RelsA8 := restrictWords (subsetOf 5 [0, 1]) relsN0A8

@[expose] def n0EnumL3 : Bool := subsetCheck l3RelsA8 [] 400 168

@[expose] def n0EnumX : Bool := subsetCheck relsN0A8 [0, 1] 100 8

end CFSG.CGT.A8S.N0
