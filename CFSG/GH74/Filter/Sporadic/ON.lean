module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.CFSGNative.Filter.ONData
public meta import Certificates.Data.CFSGNative.Filter.ONData
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5034
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem onan_secCheck :
    (ops3 154).secCheck onanSec = true :=
  Certificates.certificate5034

theorem not_gen4_ON : ¬ Gen4 NativeSporadic.ON :=
  (spec3 154).not_gen4_of_secCheck onanSec onan_secCheck (by decide)

end CFSG.GH74.Filter
