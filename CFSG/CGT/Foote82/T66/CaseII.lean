module

public import CFSG.CGT.Foote82.T66.CitedCaseII
import CFSG.CGT.Foote82.T66.CaseII514b

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

theorem caseIIFalse (h51 : Lemma51) (hsplit : CaseIISplit) (haut : CaseIIAut) (hG1 : CaseIIG1)
    (hG2 : CaseIIG2) (hG9 : CaseIIG9) (hG10 : CaseIIG10) (hG12 : CaseIIG12)
    (h511a : CaseIILemma511a) (h511b : CaseIILemma511b) : CaseIIFalse := by
  intro V _ _ _ G L z v H₁ ψ hstd hrank hv hd
  have c : CaseII.Ctx G L z v H₁ ψ := ⟨hstd, hrank, hv, hd⟩
  exact c.prop514 hsplit haut hG1 hG2 h511b (c.prop513 hsplit haut hG1 hG2 hG9 hG10 hG12 h511a)

end CFSG.CGT.Foote82
