module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndFoote
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspG2
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspD4

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.CGT.PushingUpLit.CGT6M
open CFSG.RankThree.PartOne (ExceptionalCenterSmallPrimes)

theorem footeInspExc_of
    (hECS : ExceptionalCenterSmallPrimes) : FooteInspExc :=
  ⟨fun Q _ hQ => coverInv_g2 hECS Q hQ, fun Q _ _ hf hQ => coverInv_trialityD4 hECS Q hf hQ⟩

end CFSG.CGT.PushingUpLit.CGT6
