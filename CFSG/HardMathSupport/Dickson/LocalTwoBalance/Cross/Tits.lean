module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Cat
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Local
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6CrossRed

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator

section Tits


theorem localTwoCrossFamCat_three_tits : LocalTwoCrossFamCat 3 .tits := by
  rintro ⟨d, hv⟩ hd _ _
  have hd' : d = .tits := hd
  subst hd'
  obtain ⟨e⟩ := TitsAux.nonempty_mulEquiv_titsD_cat hv
  exact IsLocallyBalancedAbs.of_mulEquiv e TitsAux.isLocallyBalancedAbs_three_two_titsD

theorem localTwoCrossFamCat_five_tits : LocalTwoCrossFamCat 5 .tits := by
  rintro ⟨d, hv⟩ hd _ _
  have hd' : d = .tits := hd
  subst hd'
  obtain ⟨e⟩ := TitsAux.nonempty_mulEquiv_titsD_cat hv
  exact IsLocallyBalancedAbs.of_mulEquiv e TitsAux.isLocallyBalancedAbs_five_two_titsD

end Tits

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
