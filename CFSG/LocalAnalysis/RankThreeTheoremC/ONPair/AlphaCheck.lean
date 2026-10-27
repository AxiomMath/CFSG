module

public import Certificates.Data.CFSGNative.Bridge.ONGPL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.Sporadic.ON.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native
open CFSG.Sporadic.Bridge.ONGPL.Native

@[expose] def alphaW1 : List Int := [-2, 1, 2, -1, 1, 2, -2, 1, -1, -2, 2, -1, 2, 1, 2, 1]

@[expose] def alphaWordA : List Int := (List.replicate 5 alphaW1).flatten

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
