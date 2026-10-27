module

public import CFSG.LieType.SeitzGeneration.ExcAnisotropicClasses
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeCat

public section

namespace CFSG.LieType.SeitzGeneration

open TauCeti


theorem seitzExcAnisotropicF4Three_vacuous : SeitzExcAnisotropicF4Three := by
  rintro ⟨d, hv⟩ p _ _ hpd _ E _ _ ⟨_, ⟨q, hdq⟩, hp3, hr, _⟩
  obtain rfl : d = LieTypeIndex.F4 q := hdq
  obtain rfl : p = 3 := hp3
  exact absurd hr (not_rankLE2_cat_F4_three q hv (by simpa using hpd))

theorem seitzExcAnisotropicE6Three_vacuous : SeitzExcAnisotropicE6Three := by
  rintro ⟨d, hv⟩ p _ _ hpd _ E _ _ ⟨_, ⟨q, hdq⟩, hp3, hr, _⟩
  obtain rfl : d = LieTypeIndex.E6 q := hdq
  obtain rfl : p = 3 := hp3
  exact absurd hr (not_rankLE2_cat_E6_three q hv (by simpa using hpd))

theorem seitzExcAnisotropicE7Three_vacuous : SeitzExcAnisotropicE7Three := by
  rintro ⟨d, hv⟩ p _ _ hpd _ E _ _ ⟨_, ⟨q, hdq⟩, hp3, hr, _⟩
  obtain rfl : d = LieTypeIndex.E7 q := hdq
  obtain rfl : p = 3 := hp3
  exact absurd hr (not_rankLE2_cat_E7_three q hv (by simpa using hpd))

theorem seitzExcAnisotropicE8Three_vacuous : SeitzExcAnisotropicE8Three := by
  rintro ⟨d, hv⟩ p _ _ hpd _ E _ _ ⟨_, ⟨q, hdq⟩, hp3, hr, _⟩
  obtain rfl : d = LieTypeIndex.E8 q := hdq
  obtain rfl : p = 3 := hp3
  exact absurd hr (not_rankLE2_cat_E8_three q hv (by simpa using hpd))

end CFSG.LieType.SeitzGeneration
