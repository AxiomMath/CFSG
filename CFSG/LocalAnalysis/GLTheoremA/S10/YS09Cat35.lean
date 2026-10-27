module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09K23
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09K32
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat34
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM2Fact
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM9Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM10Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4LeMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFAK148G2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFAK14Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFBBorel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFBU38Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFBU38Char2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM1K14NotChevOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM3OutCyclic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM6TwoG2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM8I114C
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAssembly7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporB7
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat24

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I2023Res3 : Prop where
  rank : I2023.I2023FactD4RankTwo
  odd : I2023.I2023FactD2LocalOdd
  even : I2023.I2023FactD4BorelEven

section Ys09Cat35


theorem ys09_of_cat35_inputs
    (hLie : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264KLie p) (hD : I91T.TD4C1NotExc)
    (hU : ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isU3char2 → CatB.I1015PU3Res.I1015U3Res K)
    (hChev : I1431ChevTwoS) (hOI : I1429OuterInner) (hodd : I2015.I2015OddCentreFact)
    (hpar : I2015.I2015NoParabolicFact) (h18 : I2018Res2) (hA : I141F.I141U9Lemma) (hB : I141F.I141U9Rank)
    (hI114 : I114.I114FactB) (h155 : I155XRes) (hOdd : CatB.KMultA1.TD4OddNoG2Layer) (hsub : SubTRes)
    (h144 : I144Res) (h148 : K148InnerCentFact) (hK14 : K14SporU) (hU6 : U6Res) (h23 : I2023Res3)
    (hG2F : CatB.KG2F.G2FieldLayerS)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S10Cat34Inputs G p) : YS09 :=
  have hI3 : I1431Res3 := ⟨hChev, I1429Residual_of_I1429OuterInner hOI⟩
  have hI2023 : I2023Res :=
    { rank := h23.rank, out := I2023.I2023FactOutCyclic_holds, c1 := I2023.I2023FactC1_holds, odd := h23.odd,
      even := h23.even }
  have hI114' : I114Res := ⟨I114.I114FactA_holds, hI114, I114.I114FactC_holds⟩
  have hI2018 : I2018Res :=
    { b := h18.b, m := h18.m, odd := h18.odd, char := I2018.I2018U38Char2_holds,
      notAlt := I2018.I2018U38NotAlt_holds, cover := h18.cover, bt := I2018.I2018BorelTits_holds, core := h18.core }
  have hK148 : I148dRes := { inn := h148, g2 := K148G2SimpleFact_holds, two := K148TwoG2Fact_holds }
  have hK14' : K14Res := { sporU := hK14, notChev := K14NotChevOdd_holds, notAlt := K14NotAlt_holds }
  ys09_of_cat22_inputs ⟨KD264Gen.kd264SporS_of_B7
      (KD264Gen.B7.kd264SporAt_B_seven
          CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds), hLie⟩ td4InnThreeCentLe_holds hD (i1015OneRes_of_u3 hU)
    fun G _ _ m hctx p hp => by
      have h33 := (hin G m hctx p hp).toS10Cat33Inputs hG2F
      have h32 := h33.toS10Cat32Inputs hI2023
      have h31 := h32.toS10Cat31InputsK h144 hK148 hK14' hU6 hI3
      have h30 := h31.toS10Cat30Inputs hsub
      have h29 := h30.toS10Cat29Inputs h155 hOdd
      have h28 := h29.toS10Cat28Inputs hI114' hctx.1.simple hctx.1.kProper
      have h26 := h28.toS10Cat26Inputs hA hB
      have h25 := h26.toS10Cat25Inputs hI2018
      have h23' := h25.toS10Cat23Inputs hodd I2015.I2015LieModelFact_holds hpar hp.1.1 hp.1.2.1
      exact h23'.toS10Cat22InputsK hI3

end Ys09Cat35

end CFSG.LocalAnalysis.GLTheoremA

end
