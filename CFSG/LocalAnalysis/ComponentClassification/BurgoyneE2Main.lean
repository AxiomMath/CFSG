module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwistedE6
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneInputs

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit


theorem burgoynePropAE6E7_of_twisted (hT : BurgoyneE2TwistedE7Input ∧
    BurgoyneE2TwistedE6Input) : BurgoynePropAE6E7 := by
  intro X _ _ hX τ n p f hτ hp2 hL t ht Y hY hYO
  simp only [torusExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl
  · exact burgoynePropA_E6 hX hp2 hL ht hY hYO
  · exact burgoynePropA_twistedE6_of_twisted hT.2 hX hp2 hL ht hY hYO
  · exact burgoynePropA_E7_of_twisted hT.1 hX hp2 hL ht hY hYO

end CFSG.ComponentClassification.Burgoyne.E2
