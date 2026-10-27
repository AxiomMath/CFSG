module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat14
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YIFinal

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S12Cat16Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i171one : I171OneAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  smallBridge : StdSubSmallAt G
  l102_i148 : I148At G
  l102_i155 : I155At G p
  i1419 : I1419FourAt G
  i141 : I141DynkinAt G
  i1429 : I1429At G
  u42 : U42CatAt G
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

section Ys11Cat16

theorem S12Cat16Inputs.toS12Cat14Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ} (h : S12Cat16Inputs G p) :
    S12Cat14Inputs G p where
  noBig := D4Y.noTrialityBigAt_holds
  i171one := h.i171one
  i171two := h.i171two
  i265 := h.i265
  smallBridge := h.smallBridge
  l102_i148 := h.l102_i148
  l102_i155 := h.l102_i155
  i1419 := h.i1419
  i141 := h.i141
  i1429 := h.i1429
  u42 := h.u42
  i173 := h.i173
  i172 := h.i172
  compl := h.compl

end Ys11Cat16

end CFSG.LocalAnalysis.GLTheoremA
