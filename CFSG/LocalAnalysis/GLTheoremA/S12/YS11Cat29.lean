module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat28
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419Red

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1419Res : Prop where
  alt : K1419.I1419UpAltFact
  spor : K1419.I1419UpSporFact
  lie : K1419.I1419UpLieOddFact
  cls : K1419.I1419ClassFact
  exc : K1419.I1419ExcFact

structure S12Cat29Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  stdCover : StdSubCoverAt G
  i171one : I171OneAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

section Ys11Cat29


theorem S12Cat29Inputs.toS12Cat27Inputs
    (h19 : I1419Res) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S12Cat29Inputs G p) : S12Cat27Inputs G p where
  stdCover := h.stdCover
  i171one := h.i171one
  i171two := h.i171two
  i265 := h.i265
  i1419 := K1419.i1419_of_cases (G := G) h19.alt h19.spor h19.lie h19.cls h19.exc
  i173 := h.i173
  i172 := h.i172
  compl := h.compl

theorem ys11_of_cat29_inputs
    (hR : I1429Residual) (hU : CatB.U42Cat.U42SLevel) (hA : I141F.I141DynkinLie)
    (hB : I141F.I141RankSmall) (h155 : I155XRes) (h19 : I1419Res)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat29Inputs G p ∧ S12.CanonNbrAt G p) : YS11 :=
  ys11_of_cat28_inputs hR hU hA hB h155 fun G _ _ m hctx hF h11 p hp =>
    ⟨((hin G m hctx hF h11 p hp).1).toS12Cat27Inputs h19, (hin G m hctx hF h11 p hp).2⟩

end Ys11Cat29

end CFSG.LocalAnalysis.GLTheoremA
