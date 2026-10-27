module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Solomon.Coordinator

theorem localTwoCrossFamCat_three_reeG2 : LocalTwoCrossFamCat 3 .reeG2 := by
  rintro ⟨d, hv⟩ ⟨m, hd⟩ hc _
  change d = _ at hd
  subst hd
  exact absurd (TauCeti.LieTypeIndex.characteristic_reeG2 m) hc

section ReeF4

theorem localTwoCrossFamCat_three_reeF4 (h : ReeF4InnerThreeBalance) :
    LocalTwoCrossFamCat 3 .reeF4 :=
  localTwoCrossFamCat_reeF4_of_inner 3 (Or.inl rfl) h

theorem localTwoCrossFamCat_five_reeF4 (h : ReeF4InnerFiveBalance) :
    LocalTwoCrossFamCat 5 .reeF4 :=
  localTwoCrossFamCat_reeF4_of_inner 5 (Or.inr rfl) h

end ReeF4

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
