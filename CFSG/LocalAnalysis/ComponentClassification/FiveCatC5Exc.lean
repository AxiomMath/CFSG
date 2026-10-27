module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5ExcE6
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5ExcTri

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf

theorem fivePump_char5_G2 :
    FivePumpCharFiveClause .G2 :=
  C5Exc.fivePump_char5_of_oddLieA5For
    (C5Exc.oddLieA5For_G2 CatLeafProof.lieOrderFormulasInput)

theorem fivePump_char5_F4 :
    FivePumpCharFiveClause .F4 :=
  C5Exc.fivePump_char5_of_oddLieA5For
    (C5Exc.oddLieA5For_F4 CatLeafProof.lieOrderFormulasInput)

theorem fivePump_char5_E6 :
    FivePumpCharFiveClause .E6 :=
  C5Exc.fivePump_char5_of_oddLieA5For
    (C5Exc.oddLieA5For_E6 CatLeafProof.lieOrderFormulasInput)

theorem fivePump_char5_E7 :
    FivePumpCharFiveClause .E7 :=
  C5Exc.fivePump_char5_of_oddLieA5For
    (C5Exc.oddLieA5For_E7 CatLeafProof.lieOrderFormulasInput)

theorem fivePump_char5_E8 :
    FivePumpCharFiveClause .E8 :=
  C5Exc.fivePump_char5_of_oddLieA5For
    (C5Exc.oddLieA5For_E8 CatLeafProof.lieOrderFormulasInput)

theorem fivePump_char5_twistedE6 :
    FivePumpCharFiveClause .twistedE6 :=
  C5Exc.fivePump_char5_of_oddLieA5For
    (C5Exc.oddLieA5For_twistedE6 CatLeafProof.lieOrderFormulasInput)

theorem fivePump_char5_trialityD4 :
    FivePumpCharFiveClause .trialityD4 :=
  C5Exc.fivePump_char5_of_oddLieA5For
    (C5Exc.oddLieA5For_trialityD4 CatLeafProof.lieOrderFormulasInput)

theorem fivePump_char5_vacuous (τ : Open.StatedLieTag)
    (hτ : τ = .twistedB2 ∨ τ = .twistedG2 ∨ τ = .twistedF4 ∨ τ = .Tits) :
    FivePumpCharFiveClause τ := by
  intro S _ _ _ _ ⟨n, f, hm⟩
  have hadm := hm.admissible
  rcases hτ with rfl | rfl | rfl | rfl
  all_goals exact absurd hadm.2.2.2.1 (by norm_num)

end CFSG.ComponentClassification.SolMax.FiveCat
