module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Sporadic.J3.F2Spec
public import Certificates.Data.CFSGNative.SectionRank.J4Local
public meta import Certificates.Data.CFSGNative.SectionRank.J4Local
public meta import Certificates.Data.CFSGNative.J3.Basic
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank.J4Order

open CFSG.Blueprint CFSG.SectionRank.LocalWitness CFSG.Sporadic.J3 CFSG.Sporadic.J3.Native
  CFSG.SectionRank.Native

open scoped Matrix

abbrev rowsA : Array ℕ := rowsOfPayload 112 j4Sylow3Data.seedA

abbrev rowsB : Array ℕ := rowsOfPayload 112 j4Sylow3Data.seedB

end CFSG.SectionRank.J4Order
