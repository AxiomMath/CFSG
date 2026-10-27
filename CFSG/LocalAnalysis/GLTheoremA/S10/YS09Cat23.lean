module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.MultA3Core
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48X6
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S10Cat23Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i155x : I155X.I155XAt G p
  u48res : U48RootResidual G
  multaRes : CatB.MultA3.MultAG2Residual G
  i2023 : I2023At G
  i156 : I156At G p
  i2021 : I2021At G p
  i263 : I263UsedAt G p
  i265 : I265UsedAt G p
  i2018 : I2018At G
  i148d : I148DownAt G
  i2015 : I2015At G p
  i114 : I114At G
  i158 : I158AtK G
  i141 : I141RankAtK G
  substable : StdSubTableAt G
  i171 : I171At G
  u6d0 : U6D0RankAt G
  i14chev : I1431Chev2At G
  i144one : I144oneAt G
  i1428 : I1428At G
  i266 : I266At G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G
  i148f : I148fiveAt G
  u62t9 : U62Type9At G

end CFSG.LocalAnalysis.GLTheoremA
