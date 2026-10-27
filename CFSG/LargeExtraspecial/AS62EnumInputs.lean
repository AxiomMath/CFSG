module

public import CFSG.LargeExtraspecial.AS62Rels
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.LargeExtraspecial.AS62

open CFSG.CosetTable

abbrev relsBA4 := restrictWords (subsetOf 4 [2, 3]) relsB

abbrev rels1A4 := restrictWords (subsetOf 5 [2, 3]) rels1

abbrev rels2A4 := restrictWords (subsetOf 5 [2, 3]) rels2

@[expose] def relsBEnum : Bool := subsetCheck relsB [2, 3] 16 16

@[expose] def relsBA4Enum : Bool := subsetCheck relsBA4 [] 12 12

@[expose] def rels1Enum : Bool := subsetCheck rels1 [2, 3] 55 48

@[expose] def rels1A4Enum : Bool := subsetCheck rels1A4 [] 12 12

@[expose] def rels2Enum : Bool := subsetCheck rels2 [2, 3] 80 80

@[expose] def rels2A4Enum : Bool := subsetCheck rels2A4 [] 12 12

end CFSG.LargeExtraspecial.AS62
