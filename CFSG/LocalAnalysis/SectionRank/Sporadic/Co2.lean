module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.SectionRank.Co2
public meta import Certificates.Data.CFSGNative.SectionRank.Co2
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8012
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem Co2_elementary_three_rank_four :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Co2, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  Certificates.certificate8012

end CFSG.SectionRank
