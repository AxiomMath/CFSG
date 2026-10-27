module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FourGroups
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U38
public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S9

@[expose] def ExtraspecialD4HalfAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    Odd (Nat.card (GLAPPrimeCoreOf 3 L)) →
    (catalogIs (PSimple 3 L) S9.isTD4two → ∃ T : Subgroup G, T ≤ L ∧ IsExtraspecialTwo T 4 ∧
      ∃ t ∈ T, t ^ 2 = 1 ∧ t ∉ T ⊓ Subgroup.centralizer (T : Set G))

structure S9Cat3Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264 : I264At G p
  i91 : I91At G
  i147 : I147At G
  i264b : I264bAt G p
  list93 : I9List93At G p
  i137 : I137At G p
  i264_3 : I264At G 3
  i264b_3 : I264bAt G 3
  list93_3 : I9List93At G 3
  i137_3 : I137At G 3
  i269 : I269At G
  i117 : I117At G
  rank23 : Rank23At G
  i145 : I145UsedAt G p
  i141 : I141At G p
  i2610 : I2610At G
  i67 : I67At G p
  rank3 : Rank3AutAt G
  i107 : I107At G p
  aut : AutRank96At G
  extD4 : ExtraspecialD4HalfAt G
  i1431 : I1431ClAt G
  table : U4TableAt G

section ToS9Cat2


variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S9Cat3Inputs.toS9Cat2Inputs (h : S9Cat3Inputs G p) : S9Cat2Inputs G p :=
  ⟨h.i264, h.i91, h.i147, h.i264b, h.list93, h.i137, h.i264_3, h.i264b_3, h.list93_3, h.i137_3,
    h.i269, h.i117, h.rank23, CatB.l94TypeHyAt_holds G, h.i145, h.i141, h.i2610, h.i67, h.rank3,
    h.i107, CatB.rank2D4At_holds G, h.aut,
    CatB.extraspecialU5D4At_of_halves (CatB.extraspecialU5At_holds G) h.extD4,
    CatB.sylowU38At_holds (G := G), CatB.i81U5At_holds G, CatB.i2811At_holds G,
    CatB.i102U4At_holds G, h.i1431, h.table⟩

end ToS9Cat2

section YS07Final


theorem ys07_of_cat3_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S9Cat3Inputs G p) : YS07 :=
  ys07_of_cat2_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat2Inputs

end YS07Final

end CFSG.LocalAnalysis.GLTheoremA
