module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Main
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148DownFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14ChevFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I144Res : Prop where
  inn : K144.I144InnFact
  out : K144.I144OutFact

structure K14Res : Prop where
  sporU : K14SporU
  notChev : K14NotChevOdd
  notAlt : K14NotAlt

structure U6Res : Prop where
  fix : KU6FixCompFact
  cent : KU6CentL2eightFact

structure S10Cat32Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  g2field : CatB.KMultA1.G2FieldLayerAt G
  i2023 : I2023At G
  i156 : I156At G p
  i2021 : I2021At G p
  i263 : I263UsedAt G p
  i265 : I265UsedAt G p
  i158 : I158AtK G
  i171 : I171At G
  i1428 : I1428At G
  i266 : I266At G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G
  i148f : I148fiveAt G

section Ys09Cat32

structure I148dRes : Prop where
  inn : K148InnerCentFact
  g2 : K148G2SimpleFact
  two : K148TwoG2Fact

end Ys09Cat32

end CFSG.LocalAnalysis.GLTheoremA
