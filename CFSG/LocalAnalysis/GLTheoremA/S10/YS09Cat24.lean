module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Inner
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PU3Res
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat21

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys09Cat24

theorem i1015OneRes_of_u3
    (hU : ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isU3char2 → CatB.I1015PU3Res.I1015U3Res K) :
    I1015OneRes :=
  ⟨CatB.I1015PSp4Inner.i1015oneSp4Inner_holds, CatB.I1015PSp4Out.i1015oneSp4Out_holds,
    CatB.I1015PU3Res.i1015oneU3Rank_of_res hU⟩

end Ys09Cat24

end CFSG.LocalAnalysis.GLTheoremA
