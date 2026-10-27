module

public import Mathlib.LinearAlgebra.SpecialLinearGroup

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k V : Type} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V]

private theorem det_smulOfUnit {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (ν : kˣ) :
    LinearEquiv.det (LinearEquiv.smulOfUnit ν : V ≃ₗ[k] V) =
      ν ^ Module.finrank k V := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det ((LinearEquiv.smulOfUnit ν : V ≃ₗ[k] V) : V →ₗ[k] V) =
    (ν : k) ^ Module.finrank k V
  have hsmul : ((LinearEquiv.smulOfUnit ν : V ≃ₗ[k] V) : V →ₗ[k] V) =
      (ν : k) • (LinearMap.id : V →ₗ[k] V) := by
    ext v
    rfl
  rw [hsmul, LinearMap.det_smul, LinearMap.det_id, mul_one]

private theorem pow_bijective_of_coprime {k : Type} [Field k] [Finite k] {n : ℕ}
    (h : Nat.Coprime n (Nat.card k - 1)) : Function.Bijective (fun μ : kˣ => μ ^ n) := by
  have h' : (Nat.card kˣ).Coprime n := by
    rw [Nat.card_units]
    exact h.symm
  simpa only using h'.pow_left_bijective

theorem exists_specialLinear_smul_eq (hcop : Nat.Coprime (Module.finrank k V) (Nat.card k - 1))
    (z : V ≃ₗ[k] V) :
    ∃ (h : SpecialLinearGroup k V) (μ : k), μ ≠ 0 ∧ ∀ v, h v = μ • z v := by
  have hbij : Function.Bijective (fun μ : kˣ => μ ^ Module.finrank k V) :=
    pow_bijective_of_coprime hcop
  let d : kˣ := LinearEquiv.det z
  obtain ⟨ν, hν⟩ := hbij.surjective d⁻¹
  have hν' : ν ^ Module.finrank k V = d⁻¹ := hν
  let z' : V ≃ₗ[k] V := z.trans (LinearEquiv.smulOfUnit ν)
  have hz' : LinearEquiv.det z' = 1 := by
    rw [LinearEquiv.det_trans, det_smulOfUnit, hν', inv_mul_cancel]
  refine ⟨⟨z', hz'⟩, (ν : k), ν.ne_zero, ?_⟩
  intro v
  rfl

end CFSG.LinearAlgebra.RootGroupSL
