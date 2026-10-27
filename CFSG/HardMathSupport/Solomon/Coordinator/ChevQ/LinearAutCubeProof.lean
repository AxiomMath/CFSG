module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313In
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutD1Aut

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.LinearAutCubeProof

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Square

variable {F : Type} [Field F] [Finite F] {N : ℕ}

theorem exists_mul_self_eq_conjAut (hσ : ∀ σ : F ≃+* F, σ * σ = 1) (hN : 3 ≤ N)
    (β : MulAut (projectiveSL N F)) : ∃ B : GL (Fin N) F, β * β = conjAut N F B := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := N) hN
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform β
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · refine ⟨A * GeneralLinearGroup.map (σ : F →+* F) A, ?_⟩
    rw [pow_zero, mul_one, conjAut_mul_fieldAut_mul, hσ σ, map_one, mul_one]
  · refine ⟨A * GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.inverseTranspose A), ?_⟩
    rw [pow_one, ← sq, sq_conjAut_fieldAut_dualAut, hσ σ, map_one, mul_one]

theorem exists_conjAut_of_pow_three (hσ : ∀ σ : F ≃+* F, σ * σ = 1) (hN : 3 ≤ N)
    (β : MulAut (projectiveSL N F)) (hβ : β ^ 3 = 1) : ∃ B : GL (Fin N) F, conjAut N F B = β := by
  obtain ⟨B, hB⟩ := exists_mul_self_eq_conjAut hσ hN β
  refine ⟨B⁻¹, ?_⟩
  rw [map_inv, ← hB]
  have h : β * (β * β) = 1 := by rw [← pow_three, hβ]
  exact (eq_inv_of_mul_eq_one_left h).symm

end Square

theorem linearAutCube_holds : LinearAutCube := by
  intro F _ _ hF N hN α hα
  let e : ProjectiveSpecialLinearGroup (Fin N) F ≃* projectiveSL N F :=
    QuotientGroup.quotientMulEquivOfEq (scalars_eq_center N F).symm
  obtain ⟨B, hB⟩ := exists_conjAut_of_pow_three
    (CFSG.GH74.GLS.Stage2.Signalizer.L46E.ringAut_sq_of_card_four hF) hN (MulAut.congr e α)
    (by rw [← map_pow, hα, map_one])
  refine ⟨B, fun x y hxy => ?_⟩
  have he : ∀ z : SpecialLinearGroup (Fin N) F,
      e (z : ProjectiveSpecialLinearGroup (Fin N) F) = proj N F z := fun z =>
    QuotientGroup.quotientMulEquivOfEq_mk _ z
  have h1 : MulAut.congr e α (e (x : ProjectiveSpecialLinearGroup (Fin N) F)) =
      e (α (x : ProjectiveSpecialLinearGroup (Fin N) F)) := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  apply e.injective
  rw [← h1, ← hB, he, he, conjAut_proj]
  congr 1
  exact Subtype.ext (by rw [coe_slConjugation, hxy])

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.LinearAutCubeProof
