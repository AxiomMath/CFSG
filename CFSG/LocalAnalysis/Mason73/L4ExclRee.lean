module

public import CFSG.LocalAnalysis.Mason73.L4SylowTransport
public import CFSG.LocalAnalysis.Mason73.L4OrderTwoPart
public import CFSG.ClassicalInvolution.Orders.Ree

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow

variable {G : Type} [Group G] [Finite G] {n r p f : ℕ}


theorem false_of_lieModel_twistedG2_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n))
    (hL : CFSG.Blueprint.LieModel G .twistedG2 r p f) : False := by
  obtain ⟨-, hR⟩ := hL.reeTitsModel (by decide)
  obtain ⟨-, a, -, hfa, hcard⟩ := CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2 hR
  have h2 := factorization_two_card_of_l4Sylow (by omega) P hP
  rw [hcard, factorization_two_ordRee ⟨a, hfa⟩] at h2
  omega

end CFSG.LocalAnalysis.Mason73
