module

public import CFSG.CGT.Foote82.T66.MC1Steps
public import CFSG.CGT.Foote82.T66.CitedCaseI
import CFSG.CGT.Foote82.T66.CaseIS8
import CFSG.CGT.Foote82.T66.CaseIS6c
import CFSG.CGT.Foote82.T66.CaseIF6b
import CFSG.CGT.Foote82.T66.CitedProofs

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

theorem caseIFalse (h51 : Lemma51) (h25 : CaseIFooteLemma25) (hG10 : CaseIG10)
    (h511 : CaseILemma511) (hG6 : CaseIG6) : CaseIFalse := by
  clear h51
  intro V _ _ _ G L z v H₁ n ψ hstd hrank hv hd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by have := hd.six_le; omega⟩
  have h : CaseIAux.Hyp G L z v H₁ m ψ := ⟨hstd, hrank, hv, hd⟩
  rcases Nat.lt_or_ge m 2 with hm | hm
  · exact h.false_of_le7 (by omega) (h.smallK_of_le (by omega) hG10 h511) h25 h511
  · exact h.false_of_ge8 hm schurAltLift_holds hG6 (h.smallK_of_ge hm) h25

end CFSG.CGT.Foote82
