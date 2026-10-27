module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSL
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClU43
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClSp
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOm
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcFinal
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.false_of_oddLie_classical
    (h : GomiU42Data X J D E a) {t : StatedLieTag}
    {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ∈ classicalTags)
    (hD : StatedClassicalModel D t n p f) : False :=
  h.false_of_classical_of_families CFSG.SeitzReduction.gls3OddLieAutComponentsInput
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    (oddU42Free_PSL CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput)
    oddU42Shape_PSU oddU42Free_PSp oddU42Free_POmegaOdd oddU42Free_POmegaPlus
    oddU42Free_POmegaMinus gomiU42NoU43 hp hp2 ht hD

theorem GomiU42Data.false_of_oddLie_exceptional
    (h : GomiU42Data X J D E a) {t : StatedLieTag}
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ∈ chevalleyExceptionalTags)
    (hD : ChevalleyExceptionalModel D t p f) : False :=
  h.false_of_oddLie_exceptional' hp hp2 ht hD

theorem GomiU42Data.false_of_oddLie_reeTits
    (h : GomiU42Data X J D E a) {t : StatedLieTag}
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ∈ reeTitsTags)
    (hD : ReeTitsModel D t p f) : False :=
  h.false_of_oddLie_reeTits' hp hp2 ht hD

theorem GomiU42Data.false_of_oddLie
    (h : GomiU42Data X J D E a) (hD : OddLieType D) : False := by
  obtain ⟨t, n, p, f, hp, hp2, -, hmodel⟩ := hD
  rcases hmodel with ⟨ht, hc⟩ | ⟨-, ht, he⟩ | ⟨-, ht, hr⟩ | ⟨-, -, hs⟩
  · exact h.false_of_oddLie_classical hp hp2 ht hc
  · exact h.false_of_oddLie_exceptional hp hp2 ht he
  · exact h.false_of_oddLie_reeTits hp hp2 ht hr
  · exact hp2 hs.1

theorem gomiU42Selector_oddLie :
    GomiU42Selector fun D _ => OddLieType D :=
  fun _ _ _ _ _ _ _ h hD => (h.false_of_oddLie hD).elim

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
