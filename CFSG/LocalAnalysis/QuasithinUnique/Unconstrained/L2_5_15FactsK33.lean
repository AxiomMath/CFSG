module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsM11

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem k33LocalFacts
    : K33LocalFacts := by
  intro G _ _ K h
  rcases h with h | ⟨⟨e⟩⟩
  · exact Unc25K1.k33Facts_of_L33 h
  · exact Unc25K1.k33Facts_of_M11 e

end CFSG.QuasithinUnique
