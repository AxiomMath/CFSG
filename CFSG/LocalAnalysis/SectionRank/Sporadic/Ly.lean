module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Data.CFSGNative.SectionRank.Ly
public meta import Certificates.Data.CFSGNative.SectionRank.Ly
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8025
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem Ly_elementary_three_rank_four :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Ly, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  Certificates.certificate8025

end CFSG.SectionRank
