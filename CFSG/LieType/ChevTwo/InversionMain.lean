module

public import CFSG.LieType.ChevTwo.InversionFamilies
public import CFSG.LieType.ChevTwo.Reductions

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open

theorem chev2RankTwoInverts_of_hyps (hG2 : G2NoKlein) (hExc : ExcOnlyE6) (hE6 : E6Inverts)
    (hPlus : OrthPlusInverts) (hMinus : OrthMinusInverts) : Chev2RankTwoInverts := by
  intro S _ _ hs hna hC hnA A hA hcard hAI
  have hK : OuterKleinFour A := ⟨hA, hcard, hAI⟩
  rcases isChevTwo_iff.1 hC with hcl | hexc
  · rcases kleinFamily_of_isClassicalTwoOrG2 hG2 hnA hcl hK with hlin | hplus | hminus
    · exact linear_family_inverts hlin hK
    · exact hPlus S hplus A hK
    · exact hMinus S hminus A hK
  · exact hE6 S (hExc S hexc A hK) A hK

end CFSG.LieType.ChevTwo
