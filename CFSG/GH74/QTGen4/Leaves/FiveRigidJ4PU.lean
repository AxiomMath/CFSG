module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveJ4
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveU35

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin.H13.FiveNorm CFSG.Blueprint.NativeSporadic CFSG.Quasithin.H13.NQCat.T513

theorem fiveRigid_J4_leaf
    : FiveRigid (Carrier .J4) :=
  J4F.fiveRigid_J4

theorem fiveRigid_PU_leaf : FiveRigid U35.PU :=
  U35F.fiveRigid_PU

end CFSG.GH74.QTGen4.Leaves
