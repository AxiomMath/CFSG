module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OI

public section

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open scoped Pointwise

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

local notation "V₈" => Fin 4 ⊕ Fin 4 → GaloisField 3 1

theorem fh_orderOf_d4Proj_odd {x : spinGroup Q₄} (h : spinAction Q₄ x ^ 3 = 1) :
    Odd (orderOf (Q3T.d4Proj 𝔽₃ x)) := by
  have h3 : Q3T.d4Proj 𝔽₃ x ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : spinAction Q₄ (x ^ 3) = spinAction Q₄ 1 := by rw [map_pow, map_one]; exact h
    rw [d4Proj_eq_of_spinAction_eq h1, map_one]
  exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)

theorem fh_smul_of_cubes {a : V₈ ≃ₗ[𝔽₃] V₈} {β : MulAut (D4P 𝔽₃)} (hodd : Odd (orderOf β))
    (hβ : ∀ x : spinGroup Q₄, spinAction Q₄ x * a = a * spinAction Q₄ x →
      Odd (orderOf (Q3T.d4Proj 𝔽₃ x)) → β (Q3T.d4Proj 𝔽₃ x) = Q3T.d4Proj 𝔽₃ x)
    {u₁ u₂ u₃ : V₈ ≃ₗ[𝔽₃] V₈} (h₁ : u₁ ∈ elementaryGroup Q₄) (h₂ : u₂ ∈ elementaryGroup Q₄)
    (h₃ : u₃ ∈ elementaryGroup Q₄) (c₁ : u₁ * a = a * u₁) (c₂ : u₂ * a = a * u₂)
    (c₃ : u₃ * a = a * u₃) (p₁ : u₁ ^ 3 = 1) (p₂ : u₂ ^ 3 = 1) (p₃ : u₃ ^ 3 = 1)
    (hy : ∀ v, (u₁ * u₂ * u₃) ((u₁ * u₂ * u₃) v) = -v) :
    β • statedPointFamily (coe_quadPlus 4 𝔽₃) = statedPointFamily (coe_quadPlus 4 𝔽₃) := by
  have hK : Nat.card 𝔽₃ = 3 :=
    CFSG.ClassicalInvolution.ModelFacts.TG3.natCard_galoisField_three
  have key : ∀ u : V₈ ≃ₗ[𝔽₃] V₈, u ∈ elementaryGroup Q₄ → u * a = a * u → u ^ 3 = 1 →
      ∃ x : spinGroup Q₄, spinAction Q₄ x = u ∧
        β (Q3T.d4Proj 𝔽₃ x) = Q3T.d4Proj 𝔽₃ x := by
    intro u hu hc hp
    obtain ⟨x, hx, -⟩ := exists_spin_of_mem_elementary hu (Q3T.symm_mem_statedOmega hu)
    refine ⟨x, hx, hβ x (by rw [hx]; exact hc) (fh_orderOf_d4Proj_odd ?_)⟩
    rw [hx]
    exact hp
  obtain ⟨x₁, hx₁, hβ₁⟩ := key u₁ h₁ c₁ p₁
  obtain ⟨x₂, hx₂, hβ₂⟩ := key u₂ h₂ c₂ p₂
  obtain ⟨x₃, hx₃, hβ₃⟩ := key u₃ h₃ c₃ p₃
  have hyE : u₁ * u₂ * u₃ ∈ elementaryGroup Q₄ := mul_mem (mul_mem h₁ h₂) h₃
  have hyΩ := Q3T.symm_mem_statedOmega hyE
  obtain ⟨x, hx, hxc⟩ := exists_spin_of_mem_elementary hyE hyΩ
  have hxx : Q3T.d4Proj 𝔽₃ x = Q3T.d4Proj 𝔽₃ (x₁ * x₂ * x₃) := by
    apply d4Proj_eq_of_spinAction_eq
    rw [hx, map_mul, map_mul, hx₁, hx₂, hx₃]
  refine typeII_smul hK β hodd ⟨_, hyΩ⟩ (fun v => ?_) ?_
  · simp only [MulEquiv.apply_symm_apply]
    exact hy v
  · rw [← hxc, hxx]
    simp only [map_mul, hβ₁, hβ₂, hβ₃]

end CFSG.OddStandard.SmallF3.Omega
