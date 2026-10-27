module

public import CFSG.CGT.L5R.RelData
public import CFSG.Certificates.CosetTableColumns

public section

namespace CFSG.CGT.L5R

open CFSG.CosetTable

@[expose] def l52Enum : Bool := subsetCheckC l52Rels (List.range 10) 600 31

end CFSG.CGT.L5R
