module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.CFSGNative.SectionRank.McL
public meta import Certificates.Data.CFSGNative.SectionRank.McL
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8027
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem McL_elementary_three_rank_four :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.McL, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  Certificates.certificate8027

end CFSG.SectionRank
