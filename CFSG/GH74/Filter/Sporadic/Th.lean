module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.Filter.ThData
public meta import Certificates.Data.CFSGNative.Filter.ThData
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5037
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem th_secCheck :
    (ops2 248).secCheck thSec = true :=
  Certificates.certificate5037

theorem not_gen4_Th : ¬ Gen4 NativeSporadic.Th :=
  (spec2 248).not_gen4_of_secCheck thSec th_secCheck (by decide)

end CFSG.GH74.Filter
