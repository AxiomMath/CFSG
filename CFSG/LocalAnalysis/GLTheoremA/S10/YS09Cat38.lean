module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat37
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporL3DownBM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Red
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Red3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Red
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158Inn

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

structure I2018Res3 : Prop where
  odd : I2018.I2018OddB3
  cover : I2018.I2018U38Cover
  core : I2018.I2018ChevCore

structure S10Cat38Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i265 : I265UsedAt G p
  i158main : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X K B : Subgroup G) (x₁ x₂ : G) (L₁ L₂ : Subgroup G),
    I158HypK p X K B x₁ x₂ L₁ L₂ → GLAPLayer p (L₁ ⊓ Subgroup.centralizer ({x₂} : Set G)) ≠ ⊥ →
    p = 3 ∧ ∃ n : ℕ, Odd n ∧ 1 < n ∧
      ((catalogIs (PSimple 3 K) (S10.isU6n n) ∧ catalogIs (PSimple 3 L₁) (S10.isL2n (3 * n)) ∧
          (∃ M : Subgroup G, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set G)) M ∧
            catalogIs (PSimple 3 M) (S10.isL2n n)) ∧
          Nat.card B = 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 K)) ∨
        (catalogIs (PSimple 3 K) (S10.isTE6n n) ∧ catalogIs (PSimple 3 L₁) (S10.isU3n (3 * n)) ∧
          (∃ M : Subgroup G, GLAPComponent 3 (L₁ ⊓ Subgroup.centralizer ({x₂} : Set G)) M ∧
            catalogIs (PSimple 3 M) (S10.isU3n n)) ∧
          Nat.card B = 3 ^ 4 * Nat.card ↥(B ⊓ centModSubgroup 3 K))) ∧
      ∀ T : Subgroup G, T ≤ X → IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = ⊥
  i266 : I266At G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G

section Ys09Cat38


theorem S10Cat38Inputs.toS10Cat37Inputs
    (hR : T2021.T2021RankFact) (hF : T2021.T2021FixFact)
    (hL : T2021.T2021LayerFact) (hT : T2021.T2021TD4Fact) (hType171 : T171.T171SmallTypeFact)
    (hU42 : S171.I171SmallIsU42Fact) (hN : T1428.T1428NormFact) (hType1428 : T1428.T1428TypeFact)
    (hNonInn : T1428.T1428NonInnFact) (hField : T1428.T1428FieldFact) (hChev1428 : T1428.T1428ChevFact)
    (hExc : T1428.T1428ExcFact) (hU6f : T1428.T1428U6Fact) (hD4f : T1428.T1428D4Fact)
    (hI158 : ∀ p : ℕ, T158.T158InnFactOmega p)
    {G : Type} [Group G] [Finite G] {m p : ℕ} (hp : p ∈ Mu G m) (h : S10Cat38Inputs G p) :
    S10Cat37Inputs G p where
  i2021 := T2021.i2021_of_facts G hR hF hL hT hp.1.1 hp.1.2.1
  i265 := h.i265
  i158 := ⟨T158.i158Inn_of_facts hI158, h.i158main, T158.i158FG_of_facts hI158⟩
  i171 := T171.i171_of_facts G hType171 hU42
  i1428 := T1428.i1428_of_single_facts hN hType1428 hNonInn hField hChev1428
    CFSG.StandardType.ChevTwo.ys08_holds hExc hU6f hD4f G
  i266 := h.i266
  i263a := h.i263a

theorem ys09_of_cat38_inputs
    (hI : KD264Lie.KD264LieInputs) (hD : I91T.TD4C1NotExc)
    (hU : ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isU3char2 → CatB.I1015PU3Res.I1015U3Res K)
    (hChev : I1431ChevTwoS) (hOI : I1429OuterInner) (hodd : I2015.I2015OddCentreFact)
    (hpar : I2015.I2015NoParabolicFact) (h18 : I2018Res3) (hA : I141F.I141U9Lemma) (hB : I141F.I141U9Rank)
    (hI114 : I114.I114FactB) (h155 : I155XRes) (hOdd : CatB.KMultA1.TD4OddNoG2Layer) (hsub : SubTRes)
    (h144 : I144Res) (h148 : K148InnerCentFact) (hK14 : K14SporU) (hU6 : U6Res) (h23 : I2023Res3)
    (hG2F : CatB.KG2F.G2FieldLayerS) (h148f : K148FRes) (h263 : T263.T263FactGen)
    (h156 : ∀ p, T156.T156FactOmega p)
    (hR2021 : T2021.T2021RankFact) (hF2021 : T2021.T2021FixFact) (hL2021 : T2021.T2021LayerFact)
    (hT2021 : T2021.T2021TD4Fact) (hT171 : T171.T171SmallTypeFact) (hU42 : S171.I171SmallIsU42Fact)
    (hN1428 : T1428.T1428NormFact) (hType1428 : T1428.T1428TypeFact) (hNonInn1428 : T1428.T1428NonInnFact)
    (hField1428 : T1428.T1428FieldFact) (hChev1428 : T1428.T1428ChevFact) (hExc1428 : T1428.T1428ExcFact)
    (hU61428 : T1428.T1428U6Fact) (hD41428 : T1428.T1428D4Fact) (hI158 : ∀ p : ℕ, T158.T158InnFactOmega p)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S10Cat38Inputs G p) : YS09 :=
  ys09_of_cat37_inputs (fun p hp hp2 => KD264Lie.kd264KLie_holds hI p hp hp2) hD hU hChev hOI hodd hpar
    ⟨sporL3Down_B_holds, sporL3Down_M_holds, h18.odd, h18.cover, h18.core⟩ hA hB hI114 h155 hOdd hsub h144 h148
    hK14 hU6 h23 hG2F h148f h263 h156
    fun G _ _ m hctx p hp => (hin G m hctx p hp).toS10Cat37Inputs hR2021 hF2021 hL2021 hT2021 hT171 hU42 hN1428
      hType1428 hNonInn1428 hField1428 hChev1428 hExc1428 hU61428 hD41428 hI158 hp

end Ys09Cat38

end CFSG.LocalAnalysis.GLTheoremA

end
