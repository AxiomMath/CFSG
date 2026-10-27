module

public import CFSG.ClassicalInvolution.Asc77.AscE187P3

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem commutes_inf_S (h : E187Hyps p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {S : Sylow 2 G} {M₁ M₂ R₁ R₂ : Subgroup G} (hM₁ : M₁ ∈ Ω) (hM₂ : M₂ ∈ Ω) (hne : M₁ ≠ M₂)
    (hR₁ : R₁ ∈ RSet Ω) (hR₁M : R₁ ≤ M₁) (hR₁S : R₁ ≤ (S : Subgroup G)) (hR₂ : R₂ ∈ RSet Ω)
    (hR₂M : R₂ ≤ M₂) (hR₂S : R₂ ≤ (S : Subgroup G)) :
    Commutes (M₁ ⊓ (S : Subgroup G)) (M₂ ⊓ (S : Subgroup G)) := by
  rw [inf_S_eq_of_mem_RSet hp hΩ hM₁ hR₁ hR₁M hR₁S, inf_S_eq_of_mem_RSet hp hΩ hM₂ hR₂ hR₂M hR₂S]
  have hR₂2 : IsPGroup 2 R₁ := by
    obtain ⟨J, -, -, h2, -⟩ := mem_RSet_iff.mp hR₁
    exact h2
  have hRne : R₁ ≠ R₂ := by
    intro hR
    have := hΩ.card_le_two_of_le_inf hM₁ hM₂ hne hR₂2 hR₁M (hR ▸ hR₂M)
    have h8 := hΩ.eight_le_of_mem_RSet hp hR₁
    omega
  exact h.l67 hp hq G Ω hΩ S R₁ hR₁ R₂ hR₂ hR₁S hR₂S hRne

omit [Finite G] in
theorem ne_of_involution_ne {M₁ M₂ : Subgroup G} {y₁ y₂ : G} (h₁ : IsUniqueInvolution M₁ y₁)
    (h₂ : IsUniqueInvolution M₂ y₂) (hne : y₁ ≠ y₂) : M₁ ≠ M₂ := by
  rintro rfl
  exact hne (h₁.eq h₂)

theorem exists_orderOf_four_in_zpowers {B : Subgroup G} {b β : G} (hB : IsPGroup 2 B)
    (hBb : IsUniqueInvolution B b) (hβB : β ∈ B) (hβ1 : β ≠ 1) (hβb : β ≠ b) :
    ∃ y ∈ Subgroup.zpowers β, orderOf y = 4 := by
  have hβp : IsPGroup 2 (Subgroup.zpowers β) := hB.to_le (Subgroup.zpowers_le.mpr hβB)
  obtain ⟨n, hn⟩ := hβp.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have hn1 : n ≠ 0 := by
    rintro rfl
    apply hβ1
    rw [pow_zero, orderOf_eq_one_iff] at hn
    exact hn
  have hn2 : n ≠ 1 := by
    rintro rfl
    have hsq : β * β = 1 := by
      have := pow_orderOf_eq_one β
      rwa [hn, pow_one, pow_two] at this
    rcases hBb.unique β hβB hsq with h | h
    · exact hβ1 h
    · exact hβb h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨β ^ 2 ^ m, Subgroup.pow_mem _ (Subgroup.mem_zpowers β) _, ?_⟩
  have hdvd : 2 ^ m ∣ orderOf β := by
    rw [hn]
    exact pow_dvd_pow 2 (by omega)
  rw [orderOf_pow_of_dvd (by positivity) hdvd, hn, pow_add,
    Nat.mul_div_cancel_left _ (by positivity)]
  norm_num

end CFSG.ClassicalInvolution.Asc77
