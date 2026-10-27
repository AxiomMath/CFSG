module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzLift
public import CFSG.LocalAnalysis.StandardType.GGOutTwoCommInnerHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Even
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F2315a
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F2315b

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def SeitzCubeRest : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo S →
    ¬ (∃ d : TauCeti.ValidLieTypeIndex,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1 ∧
          Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    SeitzSimpleStmt S

section Certs


theorem seitzGen_of_rest (h : SeitzCubeRest) : SeitzGen := by
  refine seitzGen_of_simple CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo
    (fun K _ _ hK => CFSG.StandardType.isChevTwo_of_largeEvenMarking hK) ?_
  intro S _ _ hS
  by_cases hscope : ∃ d : TauCeti.ValidLieTypeIndex,
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1 ∧
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)
  · obtain ⟨d, hd, he⟩ := hscope
    intro q hq hq2 E hE hE0 _ hU
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.seitz2313Even_holds q hq hq2 S d he hd E hE
      hE0 hU
  · exact h S hS hscope

theorem i2315aAt_of_facts (h1 : SeitzCubeRest) (h2 : SeitzEvenCentre) {G : Type} [Group G]
    [Finite G] : I2315aAt G :=
  i2315aAt_of_seitzGen (seitzGen_of_rest h1) h2

theorem i2315bAt_of_facts (h : SeitzCubeRest) {G : Type} [Group G] [Finite G] : I2315bAt G :=
  i2315bAt_of_seitzGen (seitzGen_of_rest h)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
