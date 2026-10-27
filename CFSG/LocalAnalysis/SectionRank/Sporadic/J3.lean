module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.SectionRank.J3
public meta import Certificates.Data.CFSGNative.SectionRank.J3
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8021
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem J3_elementary_three_rank_three :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.J3, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 :=
  Certificates.certificate8021

end CFSG.SectionRank
