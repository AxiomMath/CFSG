module

public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalCoprime
import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalOuter
import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalThree

public section

namespace GL83.I713

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem outClauseFor_chevalleyExceptional
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (_hnonab : ∃ a b : S, a * b ≠ b * a) {t : StatedLieTag} {p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (h : ChevalleyExceptionalModel S t p f) :
    OutClauseFor S := by
  intro ℓ hℓ hℓ2 hSℓ
  obtain ⟨⟨hpp, hf, hadm⟩, hm⟩ := h
  have hcyc : IsCyclic (Outer S) → pRank ℓ (⊤ : Subgroup (Outer S)) ≤ 1 := fun _ =>
    pRank_top_le_one_of_isCyclic hℓ
  cases t
  case G2 =>
    have hadm' : 0 = 0 ∧ 3 ≤ p ^ f := hadm
    exact hcyc (isCyclic_outer_of_untwistedModel_G2 hpp hf hadm'.2 hm)
  case F4 => exact hcyc (isCyclic_outer_of_untwistedModel_F4 hpp hf hm)
  case E6 =>
    have hm' : UntwistedChevalleyModel S .E6 (p ^ f) := hm
    refine pRank_outer_le_one_of_untwistedModel_E (Or.inl rfl) hpp hm' hℓ hℓ2 fun _ hℓ3 => ?_
    subst hℓ3
    have := four_le_pRank_three_of_untwistedModel_E6 hm'
    omega
  case E7 =>
    have hm' : UntwistedChevalleyModel S .E7 (p ^ f) := hm
    exact pRank_outer_le_one_of_untwistedModel_E (Or.inr (Or.inl rfl)) hpp hm' hℓ hℓ2
      fun h6 => absurd h6 (by decide)
  case E8 =>
    have hm' : UntwistedChevalleyModel S .E8 (p ^ f) := hm
    exact pRank_outer_le_one_of_untwistedModel_E (Or.inr (Or.inr rfl)) hpp hm' hℓ hℓ2
      fun h6 => absurd h6 (by decide)
  case twistedE6 =>
    have hm' : TwistedChevalleyModel S .E6 (p ^ f) := hm
    by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      have := two_le_pRank_three_of_twistedE6Model hpp hf hm'
      omega
    · exact pRank_outer_le_one_of_twistedE6Model hpp hf hm' hℓ hℓ3
  case trialityD4 =>
    have hm' : TwistedChevalleyModel S .D4 (p ^ f) := hm
    exact hcyc (isCyclic_outer_of_trialityModel hpp hf hm')
  all_goals exact absurd ht (by simp [chevalleyExceptionalTags])

end GL83.I713
