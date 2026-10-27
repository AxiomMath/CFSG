module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import Certificates.Data.CFSGNative.SectionRank.B
public meta import Certificates.Data.CFSGNative.SectionRank.B
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8010
public import CFSG.Certificates.Kernel.BabyMonster.E35B
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem b_check :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.B, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  Certificates.certificate8010

theorem B_elementary_three_rank_four :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.B, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  CFSG.KC.BM.E35Group.elemAbelian_three_four_B

end CFSG.SectionRank
