module

public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem conj_eq_of_conj_mul_eq_of_commute {G : Type*} [Group G] {α β ρ : MulAut G} {g : G}
    (h : MulAut.conj g * ρ * α * (MulAut.conj g * ρ)⁻¹ = β) (hρβ : Commute ρ β) :
    MulAut.conj (ρ⁻¹ g) * α * (MulAut.conj (ρ⁻¹ g))⁻¹ = β := by
  have hc : MulAut.conj (ρ⁻¹ g) = ρ⁻¹ * MulAut.conj g * ρ := by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply_self]
  rw [hc]
  calc ρ⁻¹ * MulAut.conj g * ρ * α * (ρ⁻¹ * MulAut.conj g * ρ)⁻¹
      = ρ⁻¹ * (MulAut.conj g * ρ * α * (MulAut.conj g * ρ)⁻¹) * ρ := by group
    _ = ρ⁻¹ * β * ρ := by rw [h]
    _ = β := by rw [mul_assoc, ← hρβ.eq, ← mul_assoc, inv_mul_cancel, one_mul]

section F4

theorem even_F4_outer_involution_inner_conj {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f)
    (α : MulAut (adjointGroup ReeTag.F4.tag K)) (hα : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range) :
    ∃ h : adjointGroup ReeTag.F4.tag K,
      α = MulAut.conj h * ReeTag.F4.finiteExceptionalAut K ^ f * (MulAut.conj h)⁻¹ := by
  obtain ⟨ψ, hψ, -⟩ := even_F4_all_outer_involutions_canonical hf K hK α hα hαo
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF ψ
  have hcomm : Commute (ReeTag.F4.finiteExceptionalAut K ^ (k : ℕ))
      (ReeTag.F4.finiteExceptionalAut K ^ f) := (Commute.refl _).pow_pow _ _
  have key := conj_eq_of_conj_mul_eq_of_commute (hgk ▸ hψ) hcomm
  refine ⟨((ReeTag.F4.finiteExceptionalAut K ^ (k : ℕ))⁻¹ g)⁻¹, ?_⟩
  rw [map_inv, inv_inv, ← key]
  group

theorem even_F4_outer_involutions_inner_conj {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (α β : MulAut (adjointGroup .F4 K)) (hα : α ^ 2 = 1)
    (hβ : β ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range)
    (hβo : β ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range) :
    ∃ h : adjointGroup .F4 K, β = MulAut.conj h * α * (MulAut.conj h)⁻¹ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have key : ∀ α β : MulAut (adjointGroup ReeTag.F4.tag K), α ^ 2 = 1 → β ^ 2 = 1 →
      α ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range →
      β ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range →
      ∃ h : adjointGroup ReeTag.F4.tag K, β = MulAut.conj h * α * (MulAut.conj h)⁻¹ := by
    intro α β hα hβ hαo hβo
    obtain ⟨a, ha⟩ := even_F4_outer_involution_inner_conj hf K hK α hα hαo
    obtain ⟨b, hb⟩ := even_F4_outer_involution_inner_conj hf K hK β hβ hβo
    refine ⟨b * a⁻¹, ?_⟩
    rw [hb, ha, map_mul, map_inv]
    group
  exact key α β hα hβ hαo hβo

end F4

end CFSG.SeitzReduction.F4Pilot
