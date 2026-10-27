module

public import CFSG.HardMathSupport.Solomon.Proving.L3Center
public import CFSG.HardMathSupport.Solomon.Proving.PSU32Centre
public import CFSG.HardMathSupport.Solomon.LocalBalance.Extremal

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem center_eq_bot_of_isExtremalType {Y : Type} [Group Y] (hY : IsExtremalType Y) :
    Subgroup.center Y = ⊥ := by
  rcases hY with ⟨K, hF, hfin, -, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hcard, -, -, ⟨e⟩⟩
  · exact center_eq_bot_of_sl_three K Y e
  · by_cases hq2 : q = 2
    · subst hq2
      exact center_eq_bot_of_su_three_two K (by rw [hcard]; norm_num) Y e
    · exact center_eq_bot_of_su_three_ne_two Y K q hcard hq2 e

end CFSG.HardMathSupport.Solomon.Proving

end
