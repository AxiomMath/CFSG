module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL32e

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem isSylowOf_X :
    IsSylowOf 2 D.X (centralizer ({D.x} : Set G)) := by
  have hx : D.x = D.toG (SE.invRep 5) := rfl
  refine D.isSylowOf_of_classes (D.toG_mem _) (by rw [hx]; exact D.toG_invRep_mul_self 5)
    (by rw [hx]; exact D.toG_invRep_ne_one 5) fun i ⟨h, hh⟩ => ?_
  rw [D.card_X]
  by_cases hi0 : i = 0
  · subst hi0
    rw [SE.invRep_zero] at hh
    exact absurd ⟨h, hh⟩ D.not_conj_x_z
  by_cases hi1 : i = 1
  · subst hi1
    exact absurd ⟨h, hh⟩ D.not_conj_x_t
  by_cases hi2 : i = 2
  · subst hi2
    exact absurd ⟨h, hh⟩ D.not_conj_x_a1l
  exact SE.invRepCent_le_of_three_le i hi0 hi1 hi2

theorem not_conj_x_a3a4 :
    ¬ ∃ g : G, g⁻¹ * D.x * g = D.a3a4 := by
  rintro ⟨g, hg⟩
  obtain ⟨g₁, -, hC⟩ := exists_conj_extremal D.S.isPGroup' D.isSylowOf_X hg
  set K := ((D.S : Subgroup G) ⊓ centralizer ({D.a3a4} : Set G)).map
    (MulAut.conj g₁⁻¹).toMonoidHom
  have hKX : K ≤ D.X := by
    rintro _ ⟨c, hc, rfl⟩
    have := hC c hc
    change g₁⁻¹ * c * g₁⁻¹⁻¹ ∈ D.X
    rwa [inv_inv]
  have hKeq : K = D.X := eq_of_le_of_card_ge hKX (by
    rw [card_map_of_injective (MulAut.conj g₁⁻¹).injective, D.card_C_a3a4, D.card_X])
  have hay : D.ay ∈ K := hKeq ▸ D.ay_mem_X
  obtain ⟨c, hc, hcay⟩ := hay
  have hcay' : g₁⁻¹ * c * g₁ = D.ay := by
    have : g₁⁻¹ * c * g₁⁻¹⁻¹ = D.ay := hcay
    rwa [inv_inv] at this
  obtain ⟨hcS, hcC⟩ := mem_inf.mp hc
  obtain ⟨c₀, rfl⟩ := D.exists_toG hcS
  have hc₀ : c₀ * SE.invRep 3 = SE.invRep 3 * c₀ := by
    have h := mem_centralizer_singleton_iff.mp hcC
    rw [← map_mul, ← map_mul] at h
    exact D.toG_injective h
  have h4 : D.ay ^ 4 = 1 := by
    rw [← hcay', conj_pow_inv, ← map_pow, SE.pow_four_of_comm_a3a4 c₀ hc₀, map_one]
    group
  exact D.z_ne_one (D.ay_pow_four.symm.trans h4)

end GHSylow

end CFSG.ComponentClassification.GHarris
