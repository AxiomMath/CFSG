module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.CFSGNative.SectionRank.Suz
public meta import Certificates.Data.CFSGNative.SectionRank.Suz
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8030
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem Suz_elementary_three_rank_four :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Suz, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  Certificates.certificate8030

end CFSG.SectionRank
