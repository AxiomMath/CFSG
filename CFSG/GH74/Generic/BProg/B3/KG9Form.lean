module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7OddLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6PSL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6PSU
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6PSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6ExcFam

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace KG531BP

namespace KG9

open CFSG
open CFSG.ComponentClassification.CatLeafProof (A6CentreForm oddLieA6CentreFor_PSL
  oddLieA6CentreFor_PSU oddLieA6CentreFor_PSp oddLieA6CentreFor_G2 oddLieA6CentreFor_trialityD4
  oddLieA6CentreFor_twistedG2)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (GHOddLie admissible_of_lieModel
  ne_two_of_pow_mod_four')
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem a6CentreForm_of_ghOddLie {S : Type} [Group S] (h : GHOddLie S) (α : MulAut S)
    (hα : orderOf α = 2) : A6CentreForm ↥(fixedSubgroup α) := by
  obtain ⟨p, f, hp, hf, h⟩ := h
  rcases h with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, -, hm⟩ | ⟨hp2, -, hm⟩ | ⟨h3, hm⟩ |
      ⟨h1, hm⟩ | hm
  · exact oddLieA6CentreFor_PSL S _ p f hp hp2 (admissible_of_lieModel hm (by decide)) hm α hα
  · exact oddLieA6CentreFor_PSL S _ p f hp hp2 (admissible_of_lieModel hm (by decide)) hm α hα
  · exact oddLieA6CentreFor_PSU S _ p f hp hp2 (admissible_of_lieModel hm (by decide)) hm α hα
  · exact oddLieA6CentreFor_PSp S _ p f hp hp2 (admissible_of_lieModel hm (by decide)) hm α hα
  · exact oddLieA6CentreFor_G2 S _ p f hp hp2 (admissible_of_lieModel hm (by decide)) hm α hα
  · exact oddLieA6CentreFor_trialityD4 S _ p f hp hp2 (admissible_of_lieModel hm (by decide)) hm
      α hα
  · exact oddLieA6CentreFor_PSL S _ p f hp hp2 (admissible_of_lieModel hm (by decide)) hm α hα
  · exact oddLieA6CentreFor_PSU S _ p f hp hp2 (admissible_of_lieModel hm (by decide)) hm α hα
  · exact oddLieA6CentreFor_PSL S _ p f hp (ne_two_of_pow_mod_four' hf (Or.inl h3))
      (admissible_of_lieModel hm (by decide)) hm α hα
  · exact oddLieA6CentreFor_PSU S _ p f hp (ne_two_of_pow_mod_four' hf (Or.inr h1))
      (admissible_of_lieModel hm (by decide)) hm α hα
  · exact oddLieA6CentreFor_twistedG2 S _ 3 f Nat.prime_three (by norm_num)
      (admissible_of_lieModel hm (by decide)) hm α hα

end KG9

end KG531BP

end CFSG.GH74.Generic.BProg.B3
