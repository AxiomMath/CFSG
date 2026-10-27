module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentUnitary

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem exists_scalar_of_component {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) {W : Type} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hW : 1 ≤ finrank E W) {C : W →ₛₗ[h.bar] W →ₗ[E] E} (hC : C.IsSymm)
    (hCl : C.SeparatingLeft) {M : Type} [Group M] (ρ : M →* sesqUnitaryGroup C)
    (hρi : Function.Injective ρ) (hρc : IsComponent ρ.range) {ζ : E} (hζ : h.norm ζ = 1)
    (hζk : ζ ^ finrank E W = 1) : ∃ x : M, x ∈ center M ∧ unitaryOp (ρ x) = ζ • 1 := by
  obtain ⟨-, -, hr⟩ := eq_unitarySpecial_of_isComponent h hp hW hC hCl hρc
  have hζ0 : ζ ≠ 0 := ne_zero_of_norm_eq_one h hζ
  let u : LinearMap.GeneralLinearGroup E W :=
    Units.mk (ζ • 1) (ζ⁻¹ • 1)
      (by rw [smul_mul_smul_comm, mul_inv_cancel₀ hζ0, one_mul, one_smul])
      (by rw [smul_mul_smul_comm, inv_mul_cancel₀ hζ0, one_mul, one_smul])
  have hu : ((u : LinearMap.GeneralLinearGroup E W) : Module.End E W) = ζ • 1 := rfl
  let s : sesqUnitaryGroup C :=
    ⟨u, mem_sesqUnitaryGroup.mpr fun x y => by
      rw [hu]
      simp only [LinearMap.smul_apply, Module.End.one_apply]
      rw [sesq_smul_smul, hζ, one_mul]⟩
  have hs : unitaryOp s = ζ • 1 := rfl
  have hz : s ∈ sesqNormOneScalars h C := ⟨ζ, hζ, rfl⟩
  have hsSU : s ∈ unitarySpecial C := by
    rw [mem_unitarySpecial]
    change LinearMap.det (unitaryOp s) = 1
    rw [hs, LinearMap.det_smul]
    have hdet : LinearMap.det (1 : Module.End E W) = 1 := LinearMap.det_id
    rw [hdet, mul_one, hζk]
  rw [← hr] at hsSU
  obtain ⟨x, hx⟩ := hsSU
  refine ⟨x, Subgroup.mem_center_iff.mpr fun y => hρi ?_, by rw [hx, hs]⟩
  simp only [map_mul, hx]
  exact (mem_sesqNormOneScalars_commute hz (ρ y)).symm

end CFSG.OddStandard.HigherRank.LinUnit
