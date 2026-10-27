module

public import CFSG.CGT.Hall82.TheoremADefs
import CFSG.CGT.Hall82.TheoremAFacts
import CFSG.CGT.Hall82.TheoremAFibre
import CFSG.CGT.Hall82.TheoremAFusion

public section

namespace CFSG.CGT.Hall82.TheoremA

theorem hallTheoremANat_holds : HallTheoremANat := by
  intro G _ _ M θ z π h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have S := setting_of_hyps h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact S.conclusion facts_holds ⟨S.isElemAbelian facts_holds, S.conj_eq_self facts_holds⟩

end CFSG.CGT.Hall82.TheoremA
