module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSevenOutcomes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.HardMathSupport.Cooperstein
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem inClassXBlock_of_natural_seven
    (hX : CFSG.Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hN : NaturalSectionLSL S L 7) : InClassXBlock L := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  obtain ⟨θ, r, s, hr1, hs1, hrs, hD, hDX, hY3, hYS⟩ :=
    eightTen_cases_of_natural_seven hX hA hL
        (CFSG.HardMathSupport.RichardWeiss.Coordinator.center_barM_eq_bot_of_natural_seven hX hA hL
            hN) hN
  by_cases hr2 : r = 2
  · exfalso
    subst hr2
    exact eightTwo_false hA hL.toIsTwoPrimeComponent hSL
      (Proving.solvableSylowNormalizerAll G M S hX hA) (hDX M hA hL hSL symAutInner)
  · have hrg : r = 1 ∨ r = 3 ∨ 5 ≤ r := by omega
    have hsg : s = 1 ∨ s = 3 ∨ 5 ≤ s := by omega
    exact outcomeOne_of_caseA_seven hX hA hL hN (hYS hrg hsg)

end CFSG.LocalAnalysis.RankThreeTheoremC
