module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwap
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley


theorem exists_mul_ne_mul_of_mulEquiv_adjointGroup_F4 {H : Type*} [Group H] {K : Type} [Field K]
    (e : H ≃* adjointGroup .F4 K) : ∃ a b : H, a * b ≠ b * a := by
  have := CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 K
  have := CFSG.LieType.Steinberg.Adjoint.nontrivial_f4 K
  by_contra h
  refine Group.IsPerfect.not_isMulCommutative (adjointGroup .F4 K) ⟨⟨fun a b => ?_⟩⟩
  by_contra hab
  exact h ⟨e.symm a, e.symm b, fun h' => hab (e.symm.injective (by rw [map_mul, map_mul, h']))⟩

theorem false_of_simple_of_swap_F4 {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {G₁ G₂ : Subgroup G} {t : G} (ht : orderOf t = 2) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : G₁ ≃* adjointGroup .F4 K)
    (h₁₂ : G₂ ≤ centralizer (G₁ : Set G)) (hswap : G₁.map (MulAut.conj t).toMonoidHom = G₂)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) : False := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : IsSimpleGroup (adjointGroup .F4 K) :=
    CFSG.LieType.Chevalley.isSimpleGroup_of_mulEquiv_adjointGroup_F4 hf hK (MulEquiv.refl _)
  exact false_of_simple_of_swap_of_isSimpleGroup ht e.isSimpleGroup
    (exists_mul_ne_mul_of_mulEquiv_adjointGroup_F4 e) h₁₂ hswap huniq

end CFSG.SeitzReduction.F4Pilot
