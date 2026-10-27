module

public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses
public import CFSG.LieType.SeitzGeneration.ExcOuterClasses
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeTwCat

public section

namespace CFSG.LieType.SeitzGeneration

open TauCeti


theorem seitzExcAnisotropicTwistedE6Three_vacuous : SeitzExcAnisotropicTwistedE6Three := by
  rintro ⟨d, hv⟩ p _ _ hpd _ E _ _ ⟨_, ⟨q, hdq⟩, hp3, hr, _⟩
  obtain rfl : d = LieTypeIndex.twistedE6 q := hdq
  obtain rfl : p = 3 := hp3
  exact absurd hr (not_rankLE2_cat_twistedE6_three q hv (by simpa using hpd))

theorem seitzExcOuterNarrowTwistedE6Three_vacuous : SeitzExcOuterNarrowTwistedE6Three := by
  rintro ⟨d, hv⟩ p _ _ hpd _ E _ _ ⟨_, ⟨hr, _⟩, ⟨q, hdq⟩, hp3⟩
  obtain rfl : d = LieTypeIndex.twistedE6 q := hdq
  obtain rfl : p = 3 := hp3
  exact absurd hr (not_rankLE2_cat_twistedE6_three q hv (by simpa using hpd))

end CFSG.LieType.SeitzGeneration
