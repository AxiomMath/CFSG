module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33ReeTits
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33ReeLarge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33ReeSmall

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.Ree

open CFSG Subgroup

theorem not_isPGroup_of_model
    (Y : Type) [Group Y] [Finite Y] {t : Assembly.LowTwoRank.StatedLieTag} {p f : ℕ}
    (ht : t ∈ Blueprint.reeTitsTags) (hY : Blueprint.ReeTitsModel Y t p f)
    (a : MulAut Y) (ha : orderOf a = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  simp only [Blueprint.reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact smallRee_not_isPGroup_of_model Y hY a ha
  · exact largeRee_not_isPGroup_of_model Y hY a ha
  · exact tits_not_isPGroup_of_model Y hY a ha

theorem twoNilpFor_reeTits :
    TwoNilpFor (fun Y _ =>
      ∃ t p f, t ∈ Blueprint.reeTitsTags ∧ Blueprint.ReeTitsModel Y t p f) := by
  intro Y _ _ hY _ _ a ha hP
  obtain ⟨t, p, f, ht, hY⟩ := hY
  exact absurd hP (not_isPGroup_of_model Y ht hY a ha)

end CFSG.ComponentClassification.HarrisLit.L33.Ree
