module

public import CFSG.ClassicalInvolution.Asc77.AscSixEta
public import CFSG.ClassicalInvolution.Asc77.WP1Section6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem l6_8 : L6_8 p f := by
  intro hp hq G _ _ Ω hΩ S U hU hUS η hη hηS
  obtain ⟨S₁, hS₁, -⟩ := hη
  have hηS' : η ∈ etaSet Ω (S : Subgroup G) := mem_etaSet_of_le hΩ.conjInvariant hS₁ hηS
  obtain ⟨K, hK, hUK⟩ := hΩ.exists_member_of_mem_USet hp hU
  obtain ⟨V₀, hV₀, hV₀K⟩ := exists_mem_of_mem_etaSet hp hΩ hηS' hK ⟨hU, hUS⟩ hUK
  have hV₀U : V₀ ∈ USet Ω := (hS₁.1 hV₀).1
  have hT : IsPGroup 2 ↥(U ⊔ V₀) := S.isPGroup'.to_le (sup_le hUS (hηS V₀ hV₀))
  have hdich := hΩ.eq_or_sup_mem_RSet hp hK hU hV₀U hUK hV₀K hT
  have hlie : ∀ V : Subgroup G, (U = V ∨ U ⊔ V ∈ RSet Ω) → V ≤ K := by
    intro V h
    rcases h with h | hR
    · exact h ▸ hUK
    · obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
      have hJK : J = K :=
        hΩ.eq_of_mem_USet hp hU hJ hK (le_sup_left.trans hRJ.1) hUK
      exact hJK ▸ (le_sup_right.trans hRJ.1)
  refine ⟨V₀, ⟨hV₀, ?_⟩, ?_⟩
  · rcases hdich with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro V₁ ⟨hV₁, h₁⟩
    by_contra hne
    exact hS₁.2.1 V₁ hV₁ V₀ hV₀ hne K hK ⟨hlie V₁ h₁, hV₀K⟩

end CFSG.ClassicalInvolution.Asc77
