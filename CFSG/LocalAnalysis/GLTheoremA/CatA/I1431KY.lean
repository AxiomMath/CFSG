module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YCase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Red

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section MainCerts


theorem in8910_i1431_of_factsK (hSpor : CFSG.LocalAnalysis.GLTheoremA.I1431SporSK)
    (hChev : CFSG.LocalAnalysis.GLTheoremA.I1431ChevTwoS)
    (h1429 : CFSG.LocalAnalysis.GLTheoremA.I1429Residual)
    (hD4 : I1431YD4Two) (hU5 : I1431YU5Two) (hU4 : I1431YU4Eight) (G : Type) [Group G] [Finite G] :
    S8.L89.I1431At G := by
  have hC : CFSG.LocalAnalysis.GLTheoremA.I1431ClAt G :=
    CFSG.LocalAnalysis.GLTheoremA.i1431ClAt_of_XK hSpor hChev G
      (CFSG.LocalAnalysis.GLTheoremA.i1429At_of_residual h1429 G)
  unfold S8.L89.I1431At
  intro a y J I K T hctx
  have h1 := conj1_of_clat hC a y J I hctx
  exact ⟨h1, fun hloc => conj2_of_facts hD4 hU5 hU4 hctx hloc h1⟩

end MainCerts

end CFSG.LocalAnalysis.GLTheoremA.I1431Y

end
