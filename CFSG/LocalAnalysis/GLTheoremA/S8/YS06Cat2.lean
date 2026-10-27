module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112a
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112b
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KDOutUsers

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.Coordinator

namespace S8

structure Inputs84Cat2 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1016 : L84.I1016ONAt G
  i1425 : L84.I1425At G
  i1430 : L84.I1430At G
  i106 : L84.I106T1430At G
  i1431 : L84.I1431At G
  kfacts : L84.KFactsAt G
  onfacts : L84.ONFactsAt G

structure Inputs8910Cat2 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  cfgI : L89.CfgIAt G p
  i301B : L89.I301BAt G p
  i1420 : L89.I1420CfgAt G p
  i1016 : L89.I1016At89 G
  i1431 : L89.I1431At G
  i2016 : L89.I2016At G
  i1432 : L89.I1432At G

end S8

structure S8Cat2Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i66 : I66At
  i1017 : I1017At G p
  i1016Row : I1016RowAt G p
  i301A : I301AAt G p
  timmesfeld : TimmesfeldAt
  no5Pumpup : No5PumpupAt
  i1016Co2 : I1016Co2At G
  in83 : S8.Inputs83Cat G p
  in84 : S8.Inputs84Cat2 G p
  in8910 : S8.Inputs8910Cat2 G p


variable {G : Type} [Group G] [Finite G] {p : ℕ}

namespace S8

theorem Inputs84Cat2.toInputs84Cat
    (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G)
    (h : Inputs84Cat2 G p) : Inputs84Cat G p :=
  ⟨h.i1016, h.i1425, input18_3_4_holds, L84.i112At_holds hsimple hKP, h.i1430, h.i106, h.i1431,
    h.kfacts, h.onfacts, lBalanceAt_holds G 3 Nat.prime_three⟩

theorem Inputs8910Cat2.toInputs8910
    (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G)
    (h : Inputs8910Cat2 G p) : Inputs8910 G p :=
  ⟨⟨⟨h.cfgI, h.i301B⟩, input18_3_4_holds, i112StarAt_holds G p, i112RankAt_holds G,
    L89.i112NormAt_holds hsimple hKP p, h.i1420, h.i1016, h.i1431, i71InnerAt_holds G, h.i2016,
    h.i1432⟩⟩

end S8

theorem S8Cat2Inputs.toS8CatInputs
    {m : ℕ} (hctx : ThmACtx G m) (h : S8Cat2Inputs G p) :
    S8CatInputs G p :=
  ⟨CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds, h.i66, h.i1017, h.i1016Row,
    h.i301A, h.timmesfeld, h.no5Pumpup, h.i1016Co2, h.in83,
    h.in84.toInputs84Cat hctx.1.simple hctx.1.kProper,
    h.in8910.toInputs8910 hctx.1.simple hctx.1.kProper⟩

theorem ys06_of_cat2_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S8Cat2Inputs G p) : YS06 :=
  ys06_of_cat_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS8CatInputs hctx

end CFSG.LocalAnalysis.GLTheoremA
