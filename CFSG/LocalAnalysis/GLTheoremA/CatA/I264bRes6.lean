module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bRes5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2HoldsB

public section

namespace CFSG.LocalAnalysis.GLTheoremA

structure I264bResidual6 : Prop where
  lin : HDesc.LinearRes
  uni : HDesc.UnitaryRes
  td4 : HDesc.TD4Res

section I264bRes6


theorem i264bResidual5_of_6 (hN3 : KD264Lie.KD264InnGood) (h : I264bResidual6) : I264bResidual5 :=
  ⟨HDesc.kDescFamRes_linear_of_res hN3 h.lin, HDesc.kDescFamRes_unitary_of_res hN3 KD264Lie.kd264I5Low_holds h.uni,
    HDesc.kDescFamRes_symplectic_holds, HDesc.kDescFamRes_omegaPlus_holds, HDesc.kDescFamRes_omegaMinus_holds,
    HDesc.kDescFamRes_e6_holds, HDesc.kDescFamRes_e7_holds, HDesc.kDescFamRes_e8_holds, HDesc.kDescFamRes_f4_holds,
    HDesc.kDescFamRes_g2_holds, HDesc.kDescFamRes_twE6_holds,
    HDesc.kDescFamRes_triD4_of_res (HDesc.td4Alt_of_goodSub h.td4), HDesc.kDescFamRes_reeTits_holds⟩

end I264bRes6

end CFSG.LocalAnalysis.GLTheoremA

end
