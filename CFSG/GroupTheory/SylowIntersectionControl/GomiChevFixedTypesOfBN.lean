module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiBender
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevFixedTypes
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevHasBN
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcInvolution
public import CFSG.LieType.ChevTwo.ModelSplit
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevIsolatedOfFixed
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevFixedConnBN
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevFixedTypesExc

public section

namespace CFSG.GroupTheory

theorem gomiChevFixedTypes_of_gomiChevHasBN (hB : GomiBender) (hRad : GomiChevRadical)
    (hSplit : CFSG.LieType.ChevTwo.ChevTwoModelSplit) (hBN : GomiChevHasBN)
    (hExc : GomiChevExcInvolution) : GomiChevFixedTypes := by
  intro G _ _ L I U hL h1 hI hIL hU hIU horb
  rcases hSplit (↥L ⧸ Subgroup.center ↥L) hL.isChevTwo with hLie | hTits | hA6 | hU33
  · obtain ⟨Q, hQ⟩ := hU
    obtain ⟨N, hN, S, hTS⟩ := hBN ↥L hL hLie Q
    have : (CFSG.GH74.BNPair.cartan (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)) N).Normal :=
      hN
    exact not_isPIsolatedOver_of_eqvGen_gomiChevFixedLink hRad hL hI hIL
      fun V hV hIV => eqvGen_gomiChevFixedLink_of_isBNPair hTS hQ hIL hIU horb hV hIV
  · exact not_isPIsolatedOver_of_gomiChevExcInvolution hB hExc hL (Or.inl hTits) h1 hI hIL
      hU hIU horb
  · exact not_isPIsolatedOver_of_gomiChevExcInvolution hB hExc hL (Or.inr (Or.inl hA6)) h1
      hI hIL hU hIU horb
  · exact not_isPIsolatedOver_of_gomiChevExcInvolution hB hExc hL (Or.inr (Or.inr hU33)) h1
      hI hIL hU hIU horb

theorem gomiChevIsolated_of_gomiChevHasBN (hBT : GomiChevBorelTits) (hB : GomiBender)
    (hOrb : GomiChevAtomOrbit) (hSwap : GomiChevSwap) (hRad : GomiChevRadical)
    (hSplit : CFSG.LieType.ChevTwo.ChevTwoModelSplit) (hBN : GomiChevHasBN)
    (hExc : GomiChevExcInvolution) : GomiChevIsolated :=
  gomiChevIsolated_of_gomiChevFixedTypes hBT hB hOrb hSwap
    (gomiChevFixedTypes_of_gomiChevHasBN hB hRad hSplit hBN hExc)

end CFSG.GroupTheory
