module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat36
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263I263
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S10Cat37Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i2021 : I2021At G p
  i265 : I265UsedAt G p
  i158 : I158AtK G
  i171 : I171At G
  i1428 : I1428At G
  i266 : I266At G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G

section Ys09Cat37


theorem S10Cat37Inputs.toS10Cat36Inputs
    (hF : T263.T263FactGen) (hF156 : ∀ p, T156.T156FactOmega p) {G : Type}
    [Group G] [Finite G] {m p : ℕ} (hctx : ThmACtx G m) (hp : p ∈ Mu G m) (h : S10Cat37Inputs G p) :
    S10Cat36Inputs G p where
  i156 := T156.i156At_of_facts' hF156 G m hctx p hp
  i2021 := h.i2021
  i263 := T263.i263_of_facts' hF G hctx hp
  i265 := h.i265
  i158 := h.i158
  i171 := h.i171
  i1428 := h.i1428
  i266 := h.i266
  i263a := h.i263a

theorem ys09_of_cat37_inputs
    (hLie : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264KLie p) (hD : I91T.TD4C1NotExc)
    (hU : ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isU3char2 → CatB.I1015PU3Res.I1015U3Res K)
    (hChev : I1431ChevTwoS) (hOI : I1429OuterInner) (hodd : I2015.I2015OddCentreFact)
    (hpar : I2015.I2015NoParabolicFact) (h18 : I2018Res2) (hA : I141F.I141U9Lemma) (hB : I141F.I141U9Rank)
    (hI114 : I114.I114FactB) (h155 : I155XRes) (hOdd : CatB.KMultA1.TD4OddNoG2Layer) (hsub : SubTRes)
    (h144 : I144Res) (h148 : K148InnerCentFact) (hK14 : K14SporU) (hU6 : U6Res) (h23 : I2023Res3)
    (hG2F : CatB.KG2F.G2FieldLayerS) (h148f : K148FRes) (h263 : T263.T263FactGen)
    (h156 : ∀ p, T156.T156FactOmega p)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S10Cat37Inputs G p) : YS09 :=
  ys09_of_cat36_inputs hLie hD hU hChev hOI hodd hpar h18 hA hB hI114 h155 hOdd hsub h144 h148 hK14 hU6 h23 hG2F h148f
    fun G _ _ m hctx p hp => (hin G m hctx p hp).toS10Cat36Inputs h263 h156 hctx hp

end Ys09Cat37

end CFSG.LocalAnalysis.GLTheoremA
