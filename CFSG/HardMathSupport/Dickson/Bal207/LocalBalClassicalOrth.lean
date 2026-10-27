module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthEight
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwo

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

section Row

theorem bal207LocalBalRow_orth : Bal207LocalBalRow FamOrth := by
  rintro p ⟨d, hv⟩ ⟨hidx, horth⟩
  cases d with
  | D r q =>
    obtain ⟨rfl, hr⟩ := hidx
    rcases hr with ⟨hq, he, h6⟩ | ⟨hq, rfl⟩
    · rcases hq with hq | hq
      · exact OrthRow.Two.isLocallyBalancedAbs_three_one_catD_two r q hv h6 he hq.1 hq.2
      · exact OrthRow.isLocallyBalancedAbs_three_one_catD_eight r q hv h6 he hq.1 hq.2
    · exact OrthRow.Two.isLocallyBalancedAbs_three_one_catD4_two q hv hq.1 hq.2
  | twistedD r q =>
    obtain ⟨rfl, hq, ho, h5⟩ := hidx
    have hno : ¬ Even r := Nat.not_even_iff_odd.2 ho
    rcases hq with hq | hq
    · exact OrthRow.Two.isLocallyBalancedAbs_three_one_cattwistedD_two r q hv h5 hno hq.1 hq.2
    · exact OrthRow.isLocallyBalancedAbs_three_one_cattwistedD_eight r q hv h5 hno hq.1 hq.2
  | _ => exact horth.elim

end Row

end CFSG.HardMathSupport.Dickson.Bal207

end
