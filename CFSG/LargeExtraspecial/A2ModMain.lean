module

public import CFSG.LargeExtraspecial.A2ModHubMain
public import CFSG.LargeExtraspecial.A2ModNDefs

public section

namespace CFSG.LargeExtraspecial

open Module CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem s12ExcModuleInputN : S12ExcModuleInputN := by
  intro X _ _ τ hτ hX D hD V _ _ _ Q ρ hA
  exact A2Mod.exceptional_false hτ hX hD hA

theorem s12PSLModuleInputN : S12PSLModuleInputN := by
  intro X _ _ m hm hX D hD V _ _ _ Q ρ hA hirr
  by_contra hlt
  have hV : 10 ≤ finrank (ZMod 2) V := by omega
  rcases A2Mod.irreducible_classify hD hA hirr hV with ⟨k, -, -, hk⟩ | hle
  · exact A2Mod.Ord.lieModel_PSL_false_of_POmega hX hk
  · exact absurd hle (not_le.mpr
      (A2Mod.Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inl ⟨hm, hX⟩)))

theorem s12SpModuleInputN : S12SpModuleInputN := by
  intro X _ _ m hm hX D hD V _ _ _ Q ρ hA hirr
  by_contra hlt
  have hV : 10 ≤ finrank (ZMod 2) V := by omega
  rcases A2Mod.irreducible_classify hD hA hirr hV with ⟨k, -, -, hk⟩ | hle
  · exact A2Mod.Ord.lieModel_PSp_false_of_POmega hX hk
  · exact absurd hle (not_le.mpr
      (A2Mod.Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inl hX))))

theorem s12OmegaModuleInputN : S12OmegaModuleInputN := by
  intro X _ _ m hm hX D hD V _ _ _ Q ρ hA hirr
  by_contra hlt
  rw [not_or, not_lt] at hlt
  obtain ⟨hV, hne⟩ := hlt
  have hlt12 : 12096 < Nat.card X := by
    rcases hX with h | h
    · exact A2Mod.Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inr (Or.inl h)))
    · exact A2Mod.Ord.twelve_thousand_lt_card_of_lieModel_classical (Or.inr (Or.inr (Or.inr h)))
  rcases A2Mod.irreducible_classify hD hA hirr hV with ⟨k, -, hdim, hk⟩ | hle
  · exact hne (by rw [hdim, A2Mod.Ord.eq_of_lieModel_POmega hk hX])
  · omega

end CFSG.LargeExtraspecial
