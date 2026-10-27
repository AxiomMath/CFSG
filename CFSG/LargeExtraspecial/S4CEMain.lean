module

public import CFSG.LargeExtraspecial.S4CESpCases
public import CFSG.LargeExtraspecial.S4CEOmega
public import CFSG.LargeExtraspecial.S4CESmall

public section

namespace CFSG.LargeExtraspecial.S4

open Module Subgroup

universe u

theorem centralExtInput :
    CentralExtInput.{u} := by
  intro V _ _ _ X E₀ a ha hpair K _ _ π E hrange hcen hinf hmap hgen hnorm hwc
  have h : CEHyp π E a X E₀ := ⟨hrange, hcen, hinf, hmap, hgen, hnorm⟩
  rcases hpair with hlin | hsp | hA6 | hΩ
  · exact Or.inl (ker_eq_bot_of_naturalPair_lin ha hlin h)
  · exact Or.inl (ker_eq_bot_of_naturalPair_sp ha hsp h)
  · exact centralExtInput_of_a6Pair ha hA6 h
  · obtain ⟨h4, Q, hQ, hQa, hX, hE₀⟩ := hΩ
    obtain ⟨m, hm⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
    rcases Nat.lt_or_ge (finrank (ZMod 2) V) 6 with hlt | h6
    · have h4' : finrank (ZMod 2) V = 4 := by omega
      exact centralExtInput_of_omegaPair_four ha h4' hQ hQa hX hE₀ h
    · exact centralExtInput_omega V X E₀ a ha h6 ⟨h4, Q, hQ, hQa, hX, hE₀⟩ K π E hrange hcen
        hinf hmap hgen hnorm hwc

end CFSG.LargeExtraspecial.S4
