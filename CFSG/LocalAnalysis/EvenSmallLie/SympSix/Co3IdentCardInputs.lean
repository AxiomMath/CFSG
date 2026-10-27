module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDefs
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDefs
public meta import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.CosetTable

abbrev relsV1 := restrictWords (subsetOf _ [0, 1, 2, 4, 5, 6]) relsV

abbrev relsV2 := restrictWords (subsetOf _ [0, 2, 3, 4, 5]) relsV1

end CFSG.EvenSmallLie.SympSix.Co3Ident
