module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwE6Close
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwE6Exists

open CFSG.Blueprint.Chevalley

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



theorem subfieldMaximalAllOddTwE6 : SubfieldMaximalAllOddTwE6 := by
  intro ℓ f hℓ hf K _ _ hK σ hσ p hp hp2 hpℓ η hη M hRM
  have hS : TwE6Setup K σ η p := TwE6Setup.of_data hℓ hf hK hσ hp hp2 hpℓ hη
  by_cases hM : M = twR σ η
  · exact Or.inl hM
  right
  obtain ⟨g, hgM, hgR⟩ : ∃ g ∈ M, g ∉ twR σ η := by
    by_contra h
    push Not at h
    exact hM (le_antisymm (fun g hg => h g hg) hRM)
  obtain ⟨θ, hθ⟩ := exists_maxHeightRoot Tag.E6
  obtain ⟨r, hr, r', hr', t, hσt, hηt, hmem⟩ := exists_irrational_longRootElt_twE6 hS hθ g hgR
  have hgg : r * g * r' ∈ M := M.mul_mem (M.mul_mem (hRM hr) hgM) (hRM hr')
  have hHM := twPair_le hRM hgg
  have hHtop := twE6_eq_top_of_irrational hS hθ (twPair σ η (r * g * r')) (twR_le_twPair σ η _) hσt
    hηt hmem
  exact eq_top_iff.2 (hHtop ▸ hHM)

theorem subfieldMaximalAllTwE6 : SubfieldMaximalAllTwE6 := subfieldMaximalAllOddTwE6.toAll

theorem subfieldMaximalAllThreeTwE6 : SubfieldMaximalAllThreeTwE6 := subfieldMaximalAllOddTwE6.toThree

theorem subfieldMaximalLeOneTwE6 : SubfieldMaximalLeOneTwE6 :=
  subfieldMaximalAllTwE6.toLeOne

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
