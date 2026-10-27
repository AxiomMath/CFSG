module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.CFSGNative.SectionRank.ON
public meta import Certificates.Data.CFSGNative.SectionRank.ON
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8028
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem ON_elementary_three_rank_four :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.ON, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  Certificates.certificate8028

end CFSG.SectionRank
