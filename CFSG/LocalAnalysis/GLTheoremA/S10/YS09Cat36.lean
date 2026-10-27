module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat35
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FF

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure K148FRes : Prop where
  g2 : K148FG2CompFact
  two : K148FTwoFact
  lang : K148FLangFact
  c1 : K148FC1LayerFact

structure S10Cat36Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i156 : I156At G p
  i2021 : I2021At G p
  i263 : I263UsedAt G p
  i265 : I265UsedAt G p
  i158 : I158AtK G
  i171 : I171At G
  i1428 : I1428At G
  i266 : I266At G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G

section Ys09Cat36


theorem S10Cat36Inputs.toS10Cat34Inputs
    (h148f : K148FRes) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S10Cat36Inputs G p) : S10Cat34Inputs G p where
  i156 := h.i156
  i2021 := h.i2021
  i263 := h.i263
  i265 := h.i265
  i158 := h.i158
  i171 := h.i171
  i1428 := h.i1428
  i266 := h.i266
  i263a := h.i263a
  i148f := K148F.i148five_of_facts G h148f.g2 h148f.two h148f.lang h148f.c1

theorem ys09_of_cat36_inputs
    (hLie : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264KLie p) (hD : I91T.TD4C1NotExc)
    (hU : ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isU3char2 → CatB.I1015PU3Res.I1015U3Res K)
    (hChev : I1431ChevTwoS) (hOI : I1429OuterInner) (hodd : I2015.I2015OddCentreFact)
    (hpar : I2015.I2015NoParabolicFact) (h18 : I2018Res2) (hA : I141F.I141U9Lemma) (hB : I141F.I141U9Rank)
    (hI114 : I114.I114FactB) (h155 : I155XRes) (hOdd : CatB.KMultA1.TD4OddNoG2Layer) (hsub : SubTRes)
    (h144 : I144Res) (h148 : K148InnerCentFact) (hK14 : K14SporU) (hU6 : U6Res) (h23 : I2023Res3)
    (hG2F : CatB.KG2F.G2FieldLayerS) (h148f : K148FRes)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S10Cat36Inputs G p) : YS09 :=
  ys09_of_cat35_inputs hLie hD hU hChev hOI hodd hpar h18 hA hB hI114 h155 hOdd hsub h144 h148 hK14 hU6 h23 hG2F
    fun G _ _ m hctx p hp => (hin G m hctx p hp).toS10Cat34Inputs h148f

end Ys09Cat36

end CFSG.LocalAnalysis.GLTheoremA
