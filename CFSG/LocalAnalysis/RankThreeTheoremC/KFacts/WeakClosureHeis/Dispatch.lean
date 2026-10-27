module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.S11d.PlaneCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

section Dispatch

theorem sylowDichotomy_of_cases (hAlt : SDAlt) (hLie : SDLie) (hSpor : SDSpor) : SylowDichotomy := by
  intro K _ _ hs hnab hcat p hp h5 hpK
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, -, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | hspor
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact SylowDichotomyAt.of_mulEquiv hp e (hAlt n hn5 p hp h5)
  · exact hLie K hs hnab t n ℓ f hadm hmodel p hp h5 hpK
  · exact hSpor K hs hnab hspor p hp h5 hpK

end Dispatch

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
