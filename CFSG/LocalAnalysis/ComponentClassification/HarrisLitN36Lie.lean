module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieOdd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieEven

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem rowFor_lieModel
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hA : EvenLieInvolutionOddCoreFact) (hB : EvenLieOuterCoverFact)
    (hC : PSLTwoOddCharacteristicFact) (hD : L4U4PartialCoverFact)
    (hGA : TBLit.GriessMultipliersAllModels) :
    RowFor fun Y _ => ∃ (t : StatedLieTag) (n r f : ℕ), Blueprint.LieModel Y t n r f := by
  intro G _ _ p m τ K h ⟨t, n, r, f, hL⟩
  by_cases hr2 : r = 2
  · subst hr2
    exact h.concl_of_evenLie hA hB hL
  · exact h.concl_of_oddLie hGLS hC hD hGA hr2 hL

theorem rowFor_classicalRep
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hA : EvenLieInvolutionOddCoreFact) (hB : EvenLieOuterCoverFact)
    (hC : PSLTwoOddCharacteristicFact) (hD : L4U4PartialCoverFact)
    (hGA : TBLit.GriessMultipliersAllModels) :
    RowFor Milestones.ClassicalRep := by
  intro G _ _ p m τ K h ⟨t, n, r, f, hm⟩
  refine rowFor_lieModel hGLS hA hB hC hD hGA G p m τ K h ⟨t, n, r, f, Or.inl ⟨?_, hm⟩⟩
  cases t <;> first | decide | exact hm.2.elim

theorem rowFor_exceptionalRep
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hA : EvenLieInvolutionOddCoreFact) (hB : EvenLieOuterCoverFact)
    (hC : PSLTwoOddCharacteristicFact) (hD : L4U4PartialCoverFact)
    (hGA : TBLit.GriessMultipliersAllModels) :
    RowFor Blueprint.ExceptionalRep := by
  intro G _ _ p m τ K h hex
  rcases hex with ⟨t, r, f, ht, hm⟩ | ⟨t, r, f, ht, hm⟩ | ⟨r, f, hm⟩
  · exact rowFor_lieModel hGLS hA hB hC hD hGA G p m τ K h
      ⟨t, 0, r, f, Or.inr (Or.inl ⟨rfl, ht, hm⟩)⟩
  · exact rowFor_lieModel hGLS hA hB hC hD hGA G p m τ K h
      ⟨t, 0, r, f, Or.inr (Or.inr (Or.inl ⟨rfl, ht, hm⟩))⟩
  · exact rowFor_lieModel hGLS hA hB hC hD hGA G p m τ K h
      ⟨.twistedB2, 0, r, f, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hm⟩))⟩

end CFSG.ComponentClassification.HarrisLit.N36
