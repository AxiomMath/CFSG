module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.SectionRank.Co1
public meta import Certificates.Data.CFSGNative.SectionRank.Co1
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8011
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem Co1_elementary_three_rank_four :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Co1, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  Certificates.certificate8011

end CFSG.SectionRank
