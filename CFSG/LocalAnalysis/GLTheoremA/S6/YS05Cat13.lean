module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Main
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S6Cat13Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i2017Lie : I2017LieAt G
  charThree : NoTrialityCharThreeAt G
  i196 : I196At G p
  i2019 : I2019At G p
  i248 : I248At G p
  i267 : I267At G p
  i268 : I268At G p
  i81 : I81At G p
  i2020 : I2020At G p
  i1422Char2 : I1422Char2At G
  i264ChevTwo : I264ChevTwoAt G p

end CFSG.LocalAnalysis.GLTheoremA
