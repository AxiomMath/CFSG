module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat21
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H2017LRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248M

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I2017LRes : Prop where
  cls : I2017LieClassification
  noA7 : I2017LieNoA7
  rank : I2017LieRank
  z1 : I2017LieCenterL62
  z2 : I2017LieRankCenter

structure I2020Res : Prop where
  i2020 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), I2020At G p

structure I248Res : Prop where
  i713 : GL83.I_7_13_1
  r1 : H248.RankOneFact
  core : H248.CoreFact
  l227 : H248.L227FactM

structure S6Cat22Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i196 : I196At G p
  i2019 : I2019At G p
  i267 : I267At G p
  i268 : I268At G p
  i81 : I81At G p

section Ys05Cat22

theorem S6Cat22Inputs.toS6Cat21Inputs
    (h17 : I2017LRes) (h20 : I2020Res) (h248 : I248Res) {G : Type} [Group G]
    [Finite G] {p : ℕ} (h : S6Cat22Inputs G p) : S6Cat21Inputs G p where
  i2017Lie := i2017Lie_of_facts (G := G) h17.cls h17.noA7 h17.rank h17.z1 h17.z2
  i196 := h.i196
  i2019 := h.i2019
  i248 := H248.i248_of_factsM h248.i713 h248.r1 h248.core h248.l227 G p
  i267 := h.i267
  i268 := h.i268
  i81 := h.i81
  i2020 := h20.i2020 G p

end Ys05Cat22

end CFSG.LocalAnalysis.GLTheoremA
