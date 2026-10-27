module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourE16
public import Certificates.Certificate15014

public section

namespace CFSG.ComponentClassification.RankTwoL3Four.HypII

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.PSL3Four
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

theorem l34_checkE16 :
    l34CheckWE16 ⟨l34Prog, l34SG, l34CS⟩ = true :=
  Certificates.certificate15014

theorem l34_le_of_sixteen_le'
    {E : Subgroup ↥R} (hE : IsElemAbelian 2 E) (hE16 : 16 ≤ Nat.card E) :
    E ≤ S.subgroupOf R :=
  l34_le_of_sixteen_le l34_checkE16 hE hE16

end CFSG.ComponentClassification.RankTwoL3Four.HypII
