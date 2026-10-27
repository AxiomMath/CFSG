module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.CGT.T75B

section InducedAut

variable {H P : Type*} [Group H] [Group P]

theorem exists_involution_of_surjective (π : H →* P) (hπ : Function.Surjective π) (ψ : H ≃* H)
    (hψk : ∀ y, π y = 1 → π (ψ y) = 1) (hψψ : ∀ y, ψ (ψ y) = y) :
    ∃ α : MulAut P, (∀ y, α (π y) = π (ψ y)) ∧ α * α = 1 := by
  classical
  have hs : ∀ p, π (Function.surjInv hπ p) = p := Function.surjInv_eq hπ
  have key : ∀ y y', π y = π y' → π (ψ y) = π (ψ y') := by
    intro y y' h
    have h1 : π (y⁻¹ * y') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hψk _ h1
    rw [map_mul, map_inv, map_mul, map_inv] at h2
    exact inv_mul_eq_one.1 h2
  obtain ⟨a, ha⟩ : ∃ a : P → P, ∀ y, a (π y) = π (ψ y) :=
    ⟨fun p => π (ψ (Function.surjInv hπ p)), fun y => key _ _ (hs (π y))⟩
  have ham : ∀ p q, a (p * q) = a p * a q := by
    intro p q
    obtain ⟨y₁, rfl⟩ := hπ p
    obtain ⟨y₂, rfl⟩ := hπ q
    rw [← map_mul, ha, ha, ha, map_mul, map_mul]
  have hainv : ∀ p, a (a p) = p := by
    intro p
    obtain ⟨y, rfl⟩ := hπ p
    rw [ha, ha, hψψ]
  refine ⟨{ toFun := a
            invFun := a
            left_inv := hainv
            right_inv := hainv
            map_mul' := ham }, ha, ?_⟩
  ext p
  exact hainv p

end InducedAut

end CFSG.CGT.T75B
