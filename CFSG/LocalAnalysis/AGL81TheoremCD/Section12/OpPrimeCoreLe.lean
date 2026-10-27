module

public import CFSG.LocalAnalysis.AGL81TheoremC.CoprimeGamma
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem relPPrimeCore_le_of_gamma {p : ℕ} (hp : p.Prime) {M Q H E : Subgroup G}
    (hEH : E ≤ H)
    (hE : CFSG.Open.IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hΓ : CFSG.Open.rankThreeGamma 1 p E ≤ M) :
    CFSG.Open.relPPrimeCore p H ≤ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard' : p ^ (1 + 1) ≤ Nat.card E := by rw [hcard]
  exact CFSG.LocalAnalysis.AGL81TheoremC.relPPrimeCore_le_of_glbCore_le (k := 1) hE hcard' hEH hΓ

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
