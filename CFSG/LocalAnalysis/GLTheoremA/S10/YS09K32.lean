module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat32
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KChev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148DownMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6D0
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat31

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section Ys09K32


theorem S10Cat32Inputs.toS10Cat31InputsK
    (h144 : I144Res) (h148 : I148dRes) (hK14 : K14Res) (hU6 : U6Res)
    (hI3 : I1431Res3) {G : Type} [Group G] [Finite G] {p : ℕ} (h : S10Cat32Inputs G p) : S10Cat31Inputs G p where
  g2field := h.g2field
  i2023 := h.i2023
  i156 := h.i156
  i2021 := h.i2021
  i263 := h.i263
  i265 := h.i265
  i148d := i148d_of_facts G h148.inn h148.g2 h148.two
  i158 := h.i158
  i171 := h.i171
  u6d0 := KU6D0.u6d0_of_facts hU6.cent CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds G
  i14chev := i14chev_of_residualK G i1431SporSK_holds hK14.sporU hK14.notChev hK14.notAlt hI3.2
  i144one := K144.i144One_of_facts (G := G) h144.inn h144.out
  i1428 := h.i1428
  i266 := h.i266
  i263a := h.i263a
  i148f := h.i148f
  u62t9 := u62t9_of_facts hU6.fix G

end Ys09K32

end CFSG.LocalAnalysis.GLTheoremA

end
