module

public import Mathlib
public import CFSG.GH74.KGroups.L33
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL33Check
public meta import Mathlib
public meta import CFSG.GH74.KGroups.L33
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoL33Check
public import Certificates.Certificate8040

public section

namespace CFSG.ComponentClassification.RankTwoL33

open CFSG.GH74.KGroups

theorem l33_fourgen_ok :
    fourGenCheck (elemsT L33.QA) (elemsT L33.QP) = true :=
  Certificates.certificate8040

end CFSG.ComponentClassification.RankTwoL33
