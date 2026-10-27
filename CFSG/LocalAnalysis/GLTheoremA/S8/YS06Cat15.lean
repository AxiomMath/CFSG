module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YCase2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Facts
public import CFSG.LocalAnalysis.GLTheoremA.S8.Inputs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1430Res : Prop where
  cls : S8.L84.I1430Cls
  alt : S8.L84.I1430M23Alt
  suz : S8.L84.I1430M23Suz
  on : S8.L84.I1430M23ON
  chev : S8.L84.I1430M23Chev

structure I1431YRes : Prop where
  d4 : I1431Y.I1431YD4Two
  u5 : I1431Y.I1431YU5Two
  u4 : I1431Y.I1431YU4Eight

structure S8Cat15Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1017 : I1017At G p
  i1016Row : I1016RowAt G p
  i301A : I301AAt G p
  in84_i1431 : S8.L84.I1431At G
  in8910_i301B : S8.L89.I301BAt G p
  in8910_i1420 : S8.L89.I1420CfgAt G p
  in8910_i1432 : S8.L89.I1432At G

end CFSG.LocalAnalysis.GLTheoremA
