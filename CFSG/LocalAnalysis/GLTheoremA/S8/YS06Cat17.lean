module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat16
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Main
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Main2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112b

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1420Res : Prop where
  ly : H1420.I1420Ly
  co1 : H1420.I1420Co1
  suz : H1420.I1420Suz
  suzh : H1420.I1420Suzh
  m3 : H1420.I1420M3
  m5 : H1420.I1420M5

structure I1432Res : Prop where
  d4 : H1420.I1432ClsD4
  g2 : H1420.I1432ClsG2
  wd4 : H1420.I1432WitD4
  wg2 : H1420.I1432WitG2
  wfi : H1420.I1432WitFi24
  cent : H1420.I1432Cent
  bd4 : H1420.I1432BD4

structure I1431cRes : Prop where
  lie : H1431c.I1431LieS
  alt : H1431c.I1431AltS
  spor : H1431c.I1431SporS
  f4 : H1431c.I1431InspF42
  sp68 : H1431c.I1431InspSp68
  sp492 : H1431c.I1431InspSp492
  l2 : H1431c.I1431InspL2
  hn : H1431c.I1431InspHN
  mult : H1431c.I1431MultS

structure S8Cat17Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1017 : I1017At G p
  i301A : I301AAt G p
  in8910_i301B : S8.L89.I301BAt G p

section Ys06Cat17

theorem S8Cat17Inputs.toS8Cat16Inputs
    (h20 : I1420Res) (h32 : I1432Res) (h31 : I1431cRes) {G : Type} [Group G]
    [Finite G] {p : ℕ} (hs : IsSimpleGroup G) (hk : CFSG.Open.IsKProper G) (h : S8Cat17Inputs G p) :
    S8Cat16Inputs G p where
  i1017 := h.i1017
  i301A := h.i301A
  in84_i1431 := H1431c.in84_i1431_of_facts h31.lie h31.alt h31.spor h31.f4 h31.sp68 h31.sp492 h31.l2 h31.hn h31.mult G
  in8910_i301B := h.in8910_i301B
  in8910_i1420 := S8.L89.in8910_i1420_of_facts h20.ly h20.co1 h20.suz h20.suzh h20.m3 h20.m5 G p
  in8910_i1432 := S8.L89.in8910_i1432_of_facts G (S8.L89.i112NormAt_holds hs hk 3) h32.d4 h32.g2 h32.wd4 h32.wg2 h32.wfi h32.cent h32.bd4

end Ys06Cat17

end CFSG.LocalAnalysis.GLTheoremA
