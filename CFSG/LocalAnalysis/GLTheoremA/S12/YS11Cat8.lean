module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FP

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

structure S12Cat8Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i171one : I171OneAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  i269 : I269At G
  i269six : I269SixAt G
  smallBridge : StdSubSmallAt G
  noTri : FP.NoTrialityAt G
  l102_i148 : I148At G
  l102_i155 : I155At G p
  i1419 : I1419FourAt G
  i141 : I141DynkinAt G
  i1429 : I1429At G
  u42 : U42CatAt G
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

section YS11Cat8

theorem S12Cat8Inputs.toS12Cat7Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : S12Cat8Inputs G p) : S12Cat7Inputs G p where
  i171one := h.i171one
  i171two := h.i171two
  i265 := h.i265
  i269 := h.i269
  i269six := h.i269six
  smallBridge := h.smallBridge
  l102_dich := fieldDichotomyAt_of_noTriality h.noTri hp hp2
  l102_indep := fieldCentIndepAt_holds G hp hp2
  l102_i148 := h.l102_i148
  l102_i155 := h.l102_i155
  i1419 := h.i1419
  i141 := h.i141
  i1429 := h.i1429
  u42 := h.u42
  i173 := h.i173
  i172 := h.i172
  compl := h.compl

end YS11Cat8

end CFSG.LocalAnalysis.GLTheoremA
