module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.CFSGNative.SectionRank.Fi22
public meta import Certificates.Data.CFSGNative.SectionRank.Fi22
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8014
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem Fi22_elementary_three_rank_four :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Fi22, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  Certificates.certificate8014

end CFSG.SectionRank
