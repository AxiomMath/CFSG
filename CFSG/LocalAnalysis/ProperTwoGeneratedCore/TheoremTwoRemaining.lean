module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryNumeratorIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PointKernelRootProductProps

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

theorem theoremTwo_of_remaining
    (h : ∀ (G : Type) [Group G] [Finite G],
      RankOnePair.PairCommutatorGenerationTheorem G ∧ LinearSuzukiHullOddCoreTrivial G ∧
        LinearSuzukiPointKernelRootClauses G ∧ SolvableLinearCosetNormalizerTheorem G ∧
          UnitaryMonomialTheorem G) :
    CFSG.ProperTwoGeneratedCore.Assembly.TheoremTwo :=
  theoremTwo_of_parts fun G _ _ =>
    let ⟨hgen, hodd, hker, hslc, hmon⟩ := h G
    have hP := pairStabilizerRankOneTheorem_of_generation hgen.pairGenerationTheorem
    ⟨hP, rankOnePairFixedDegreeTheorem G,
      nonunitaryContradictionTheorem_of_parts hP (nonunitaryLinearDegreeTheorem_of_parts hgen hodd)
        (linearDegreeNormalizerSolvableTheorem_of_parts hgen hodd hker) hslc,
      unitaryContradictionTheorem_of_parts (unitaryNumeratorTheorem G) hmon⟩

theorem theoremTwo_of_generation
    (h : ∀ (G : Type) [Group G] [Finite G],
      RankOnePair.PairCommutatorGenerationTheorem G ∧ SolvableLinearCosetNormalizerTheorem G ∧
        UnitaryMonomialTheorem G) :
    CFSG.ProperTwoGeneratedCore.Assembly.TheoremTwo :=
  theoremTwo_of_remaining fun G _ _ =>
    let ⟨hgen, hslc, hmon⟩ := h G
    ⟨hgen, linearSuzukiHullOddCoreTrivial hgen, linearSuzukiPointKernelRootClauses hgen, hslc,
      hmon⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
