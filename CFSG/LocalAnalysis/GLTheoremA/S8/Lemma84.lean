module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace S8

structure Inputs84 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1016 : L84.I1016ONAt G
  i1425 : L84.I1425At G
  i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4
  i112 : L84.I112At G
  a6 : L84.A6FactsAt G
  i1430 : L84.I1430At G
  i106 : L84.I106T1430At G
  i1431 : L84.I1431At G
  kfacts : L84.KFactsAt G
  onfacts : L84.ONFactsAt G
  lbal : LBalanceAt G 3

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem lemma84 (hc : S8Ctx G p) (hin : Inputs84 G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (h82 : Sp82 G p B x L) :
    ¬ catalogIs (PSimple p L) (sporIs .ONan) :=
  L84.lemma84_of hc hin.i1016 hin.i1425 hin.i183 hin.i112 hin.a6 hin.i1430 hin.i106 hin.i1431 hin.kfacts
    hin.onfacts hin.lbal h82.hB h82.hxB h82.hx1 h82.hL h82.hBN h82.hcyc h82.huniq h82.hBL h82.hT

end S8

end CFSG.LocalAnalysis.GLTheoremA
