module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4E

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag BS4
open scoped commutatorElement

variable {F : Type} [Field F]

abbrev IsT12 (A : GL (Fin 4) F) : Prop :=
  (A * A = 1 ∧ finrank F (LinearMap.ker (toLin' A.val - 1)) = 2) ∨
    ∃ c : Fˣ, A * A = GeneralLinearGroup.scalar (Fin 4) c ∧ ¬ IsSquare (c : F)

theorem eq_one_of_common_roweig {A₁ A₂ : GL (Fin 4) F} {lam : F}
    (h : (A₁ : Matrix (Fin 4) (Fin 4) F) * A₂ = lam • ((A₂ : Matrix (Fin 4) (Fin 4) F) * A₁))
    {v : Fin 4 → F} (hv0 : v ≠ 0) {ν₁ ν₂ : F} (h₁ : v ᵥ* (A₁ : Matrix (Fin 4) (Fin 4) F) = ν₁ • v)
    (h₂ : v ᵥ* (A₂ : Matrix (Fin 4) (Fin 4) F) = ν₂ • v) : lam = 1 := by
  have hν : ∀ (A : GL (Fin 4) F) (ν : F), v ᵥ* (A : Matrix (Fin 4) (Fin 4) F) = ν • v → ν ≠ 0 := by
    intro A ν hA hν0
    rw [hν0, zero_smul] at hA
    apply hv0
    have := congrArg (fun w => w ᵥ* ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hA
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have e := congrArg (fun M => v ᵥ* M) h
  simp only [vecMul_smul, ← vecMul_vecMul, h₁, h₂, smul_vecMul, smul_smul] at e
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have := congrFun e i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  have hne : ν₂ * ν₁ ≠ 0 := mul_ne_zero (hν A₂ ν₂ h₂) (hν A₁ ν₁ h₁)
  have h3 : (1 - lam) * (ν₁ * ν₂ * v i) = 0 := by linear_combination this
  have h4 := (mul_eq_zero.mp h3).resolve_right
    (mul_ne_zero (by rwa [mul_comm] at hne) hi)
  linear_combination -h4

theorem coe_scalar_mul (lam : Fˣ) (A : GL (Fin 4) F) :
    ((GeneralLinearGroup.scalar (Fin 4) lam * A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (lam : F) • (A : Matrix (Fin 4) (Fin 4) F) := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, smul_eq_diagonal_mul]
  rfl

theorem sq_one_of_eig {A : GL (Fin 4) F} (hA : IsT12 A)
    (heig : (∃ v : Fin 4 → F, v ≠ 0 ∧ ∃ ν : F, (A : Matrix (Fin 4) (Fin 4) F) *ᵥ v = ν • v) ∨
      ∃ v : Fin 4 → F, v ≠ 0 ∧ ∃ ν : F, v ᵥ* (A : Matrix (Fin 4) (Fin 4) F) = ν • v) :
    A * A = 1 ∧ finrank F (LinearMap.ker (toLin' A.val - 1)) = 2 := by
  rcases hA with h | ⟨c, hc, hns⟩
  · exact h
  · exfalso
    have hc' : (A : Matrix (Fin 4) (Fin 4) F) * A = (c : F) • 1 := by
      rw [← Units.val_mul, hc, GeneralLinearGroup.coe_scalar, smul_one_eq_diagonal]
      rfl
    rcases heig with ⟨v, hv0, ν, hv⟩ | ⟨v, hv0, ν, hv⟩
    · exact hns (isSquare_of_eigvec hc' hv0 hv)
    · exact hns (isSquare_of_roweig hc' hv0 hv)

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
