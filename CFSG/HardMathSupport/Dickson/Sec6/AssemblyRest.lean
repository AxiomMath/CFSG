module

public import CFSG.HardMathSupport.Dickson.Sec6.AssemblyOpen
public import CFSG.HardMathSupport.Dickson.I271.SporGenAssemblyV2
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsMain5

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

section YS09


theorem i271OpenFamilies_of_chevQ
    (hQ : CFSG.HardMathSupport.Solomon.Coordinator.I271ChevQ) :
    CFSG.Yardstones.M67c2c3e09a6b.I271OpenFamilies :=
  have H := CFSG.HardMathSupport.Solomon.Coordinator.i271OpenFamilies_of_three
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.i271ChevPBal_holds
    CFSG.HardMathSupport.Dickson.I271.i271SporGen_holds hQ
  ⟨H.nnHatSixRank, H.nnOther, H.altDiv, H.altNdiv, H.chevPBal, H.chevPExc, H.sporGen,
    H.autBalanceON, H.onLow, H.chevQL34, H.chevQ⟩

end YS09

section YS12


theorem sec6Out_of_chevQ
    (hQ : CFSG.HardMathSupport.Solomon.Coordinator.I271ChevQ) :
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Out :=
  sec6Out_of_open (i271OpenFamilies_of_chevQ hQ)

end YS12

end CFSG.HardMathSupport.Dickson.Sec6
