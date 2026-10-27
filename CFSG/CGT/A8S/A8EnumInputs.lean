module

public import CFSG.CGT.A8S.RelData
public import CFSG.Certificates.CosetTableColumns

public section

namespace CFSG.CGT.A8S

open CFSG.CosetTable

@[expose] def a8Enum : Bool := subsetCheckC a8Rels (List.range 5) 400 15

end CFSG.CGT.A8S
