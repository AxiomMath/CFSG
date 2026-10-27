module

public import CFSG.ClassicalInvolution.Balance.BootstrapBalance

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem twoBalancedWrt_of_exactTriple_of_balance {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hloc : ∀ a ∈ T.group, a ≠ 1 → ComponentBalanceAt Ω a) : TwoBalancedWrt T.group := by
  have hA := T.isElemAbelian
  refine twoBalancedWrt_of_quotient_deltaCore_eq_bot hA.1 ?_
  intro a ha ha1 F₀ hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact T.comm_of_mem (hF₀E hf) ha
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => by
    rw [← pow_two]
    exact hA.2 f (hF₀E hf)
  show deltaCore (modOdd a F₀) = ⊥
  refine deltaCore_eq_bot_of_locallyTwoBalanced (pPrimeCore_oddQuot_eq_bot a) ?_ ?_ ?_
  · rw [card_modOdd_of_exponent_two hFC hF2, h4]
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  · intro L hL _ hfaith
    rcases hloc a ha ha1 L hL with h | h | h
    · obtain ⟨f, hf, hf1, hfc⟩ :=
        exists_mem_ne_one_centralizes_of_exactTriple T hΩ₁ hΩ₂ hΩ₃ ha hF₀E h4 (Or.inl h)
      exact absurd hfc (hfaith f hf hf1)
    · obtain ⟨f, hf, hf1, hfc⟩ :=
        exists_mem_ne_one_centralizes_of_exactTriple T hΩ₁ hΩ₂ hΩ₃ ha hF₀E h4 (Or.inr h)
      exact absurd hfc (hfaith f hf hf1)
    · exact h

end CFSG.ClassicalInvolution.Q3
