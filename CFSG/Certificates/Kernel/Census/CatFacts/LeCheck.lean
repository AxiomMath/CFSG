module

public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
public import CFSG.GH74.KGroups.Checks2

public section

namespace CFSG.Certificates.Kernel.PkEnum

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

theorem leCheck_eq_siftP {n : Nat} (QS QP : RawSchreierDatum n) :
    leCheck QS QP = QS.original.toList.all fun g => siftP QP g 0 := by
  simp only [leCheck, sift_eq_siftP]

end CFSG.Certificates.Kernel.PkEnum

end
