module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSylowGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.CentralCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.Sporadic.HS

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_quotient_of_isSporadic_hs {M : Subgroup G}
    (hHS : IsSporadic (↥M ⧸ center ↥M) .HS) : Nat.card (↥M ⧸ center ↥M) = 44352000 := by
  obtain ⟨e₀⟩ := hHS
  have e : (↥M ⧸ center ↥M) ≃* NativeSporadic.HS := e₀
  exact (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
