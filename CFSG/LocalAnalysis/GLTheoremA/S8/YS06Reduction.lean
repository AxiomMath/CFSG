module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Prop81
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma811

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.Coordinator

structure S8Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  sporOut : SporadicOuterLeTwo
  i66 : I66At
  i1017 : I1017At G p
  i1016Row : I1016RowAt G p
  i301A : I301AAt G p
  timmesfeld : TimmesfeldAt
  no5Pumpup : No5PumpupAt
  i1016Co2 : I1016Co2At G
  in83 : S8.Inputs83 G p
  in84 : S8.Inputs84 G p
  in8910 : S8.Inputs8910 G p

variable {G : Type} [Group G] [Finite G]

theorem stage8_of_inputs {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) (h3 : Stage3 G p)
    (h4o : Stage4Order G p) (h4 : Stage4 G p) (h5 : Stage5 G p) (h6 : Stage6 G p) (h7 : Stage7 G p)
    (hin : S8Inputs G p) : Stage8 G p := by
  have hc : S8Ctx G p := S8Ctx.of_ctx hctx hp h3 h4o h4 h5 h6 h7
  refine ⟨S8.prop81 hc hin.sporOut hin.i66 hin.i1017 hin.i1016Row hin.i301A hin.timmesfeld hin.no5Pumpup
    hin.in83 hin.in84 hin.in8910, ?_⟩
  intro hp3 hrk x L hx hL
  subst hp3
  exact S8.lemma811 hc hin.in8910 hin.i301A hin.i1016Co2 hrk hx hL

theorem ys06_of_inputs (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S8Inputs G p) : YS06 :=
  fun G _ _ m hctx p hp h3 h4o h4 h5 h6 h7 =>
    stage8_of_inputs hctx hp h3 h4o h4 h5 h6 h7 (hin G m hctx p hp)

end CFSG.LocalAnalysis.GLTheoremA
