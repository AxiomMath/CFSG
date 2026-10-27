module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieComp3
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevIter

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S6Cat3Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  input14_5 : Input14_5Print
  i1416 : I1416At G p
  i71i117 : I71I117At G p
  i196 : I196At G p
  i194 : I194At G p
  i2019 : I2019At G p
  i248 : I248At G p
  i267 : I267At G p
  i71u3 : I71U3At G p
  i268 : I268At G p
  i81 : I81At G p
  i2020 : I2020At G p
  nonIso : LieTypeNonIsoAt
  i1415 : I1415At G p
  i1415Nine : I1415NineAt G
  i1415Seven : I1415SevenAt G
  i1422 : I1422At G
  i2014 : I2014At G
  i2017 : I2017At G
  i1016Co : I1016CoAt G
  i264ChevTwo : I264ChevTwoAt G p
  i106L62 : I106L62At G
  i131L62 : I131L62At G

variable {G : Type} [Group G] [Finite G] {p : ℕ}

section ToS6Cat2Inputs

theorem S6Cat3Inputs.toS6Cat2Inputs_of_chevQ (hp : p.Prime) (hp2 : p ≠ 2)
    (hCQ : ChevClosureQAt G p)
    (hLQ : CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.LieQConstrainedInner p)
    (h : S6Cat3Inputs G p) : S6Cat2Inputs G p :=
  have hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier :=
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
      CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
  have hAmb : KDAmbSolv p := kdAmbSolv_holds hp hp2 u42_fixSubgroup_solvable
  ⟨h.input14_5, h.i1416,
    chevInnerAt_of hS (kdChevInner_of hp hp2 (kdCharP_of_lieQConstrainedInner hp hLQ) hAmb),
    h.i71i117, h.i196, h.i194, hCQ, h.i2019, h.i248, h.i267, h.i71u3,
    h.i268, h.i81, h.i2020, h.nonIso, h.i1415, h.i1415Nine, h.i1415Seven, h.i1422, h.i2014, h.i2017,
    h.i1016Co, h.i264ChevTwo, h.i106L62, h.i131L62⟩

end ToS6Cat2Inputs

section Ys05Cat3

theorem ys05_of_cat3_inputs
    (h3 : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieComp)
    (h5 : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ F,
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieCompsOn p F)
    (hLQ : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.LieQConstrainedInner p)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
      ∀ p ∈ Mu G m, S6Cat3Inputs G p) : YS05 :=
  ys05_of_cat2_inputs fun G _ _ m hctx p hp =>
    S6Cat3Inputs.toS6Cat2Inputs_of_chevQ hp.1.1 hp.1.2.1
      (chevClosureQAt_of_lieComp_lieComps h3 h5 hp.1.1 hp.1.2.1) (hLQ p hp.1.1 hp.1.2.1)
      (h G m hctx p hp)

end Ys05Cat3

end CFSG.LocalAnalysis.GLTheoremA
