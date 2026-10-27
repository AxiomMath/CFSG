module

public import CFSG.LieType.SeitzGeneration.ExcF4Two
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeCat

public section

namespace CFSG.LieType.SeitzGeneration

open TauCeti

@[expose] def SeitzExcOuterNarrowE6GeFive : Prop :=
  SeitzExcOuterNarrowForAt IsE6Index PrimeRange.geFive

@[expose] def SeitzExcOuterNarrowE7GeFive : Prop :=
  SeitzExcOuterNarrowForAt IsE7Index PrimeRange.geFive

@[expose] def SeitzExcOuterNarrowE8GeFive : Prop :=
  SeitzExcOuterNarrowForAt IsE8Index PrimeRange.geFive

section Proved

theorem seitzExcOuterNarrowF4Three_vacuous : SeitzExcOuterNarrowF4Three := by
  rintro ⟨d, hv⟩ p _ _ hpd _ E _ _ ⟨_, ⟨hr, _⟩, ⟨q, hdq⟩, hp3⟩
  obtain rfl : d = LieTypeIndex.F4 q := hdq
  obtain rfl : p = 3 := hp3
  exact absurd hr (not_rankLE2_cat_F4_three q hv (by simpa using hpd))

theorem seitzExcOuterNarrowE6Three_vacuous : SeitzExcOuterNarrowForAt IsE6Index PrimeRange.three := by
  rintro ⟨d, hv⟩ p _ _ hpd _ E _ _ ⟨_, ⟨hr, _⟩, ⟨q, hdq⟩, hp3⟩
  obtain rfl : d = LieTypeIndex.E6 q := hdq
  obtain rfl : p = 3 := hp3
  exact absurd hr (not_rankLE2_cat_E6_three q hv (by simpa using hpd))

theorem seitzExcOuterNarrowE7Three_vacuous : SeitzExcOuterNarrowForAt IsE7Index PrimeRange.three := by
  rintro ⟨d, hv⟩ p _ _ hpd _ E _ _ ⟨_, ⟨hr, _⟩, ⟨q, hdq⟩, hp3⟩
  obtain rfl : d = LieTypeIndex.E7 q := hdq
  obtain rfl : p = 3 := hp3
  exact absurd hr (not_rankLE2_cat_E7_three q hv (by simpa using hpd))

theorem seitzExcOuterNarrowE8Three_vacuous : SeitzExcOuterNarrowForAt IsE8Index PrimeRange.three := by
  rintro ⟨d, hv⟩ p _ _ hpd _ E _ _ ⟨_, ⟨hr, _⟩, ⟨q, hdq⟩, hp3⟩
  obtain rfl : d = LieTypeIndex.E8 q := hdq
  obtain rfl : p = 3 := hp3
  exact absurd hr (not_rankLE2_cat_E8_three q hv (by simpa using hpd))

theorem seitzExcOuterNarrowE6_of_geFive (h : SeitzExcOuterNarrowE6GeFive) :
    SeitzExcOuterNarrowE6 :=
  SeitzExcOuterNarrowFor.of_three_geFive seitzExcOuterNarrowE6Three_vacuous h

theorem seitzExcOuterNarrowE7_of_geFive (h : SeitzExcOuterNarrowE7GeFive) :
    SeitzExcOuterNarrowE7 :=
  SeitzExcOuterNarrowFor.of_three_geFive seitzExcOuterNarrowE7Three_vacuous h

theorem seitzExcOuterNarrowE8_of_geFive (h : SeitzExcOuterNarrowE8GeFive) :
    SeitzExcOuterNarrowE8 :=
  SeitzExcOuterNarrowFor.of_three_geFive seitzExcOuterNarrowE8Three_vacuous h

end Proved

end CFSG.LieType.SeitzGeneration
