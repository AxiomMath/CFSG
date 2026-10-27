module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenInr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_simConj_reflOf {ρ : V ≃ₗ[ZMod 3] V} (hρ : IsSimilitude Q ρ (-1))
    (u : V) (hu : Q u ≠ 0) :
    simConj hρ (reflOf Q u hu) =
      reflOf Q (ρ u) (by rw [hρ u]; exact mul_ne_zero (by decide) hu) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [coe_simConj, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    coe_reflOf_apply, coe_reflOf_apply]
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]
  congr 1
  rw [hρ u]
  have hadj := ff_polar_isSimilitude_neg (Q := Q) hρ u (ρ.symm x)
  rw [LinearEquiv.apply_symm_apply] at hadj
  simp only [← QuadraticMap.polarBilin_apply_apply]
  rw [hadj]
  congr 1
  field_simp
  rw [show ((-1 : (ZMod 3)ˣ) : ZMod 3) = -1 by norm_num]
  ring

theorem ff_reflOf_comm {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (huv : Q.polarBilin u v = 0) :
    reflOf Q u hu * reflOf Q v hv = reflOf Q v hv * reflOf Q u hu := by
  have hru : ((reflOf Q v hv : OGroup Q) : V ≃ₗ[ZMod 3] V) u = u := by
    rw [coe_reflOf_apply, QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply, huv,
      zero_div, zero_smul, sub_zero]
  have h := mul_reflOf_mul_inv (reflOf Q v hv) u hu
  have h' : reflOf Q v hv * reflOf Q u hu * (reflOf Q v hv)⁻¹ = reflOf Q u hu := by
    simpa [hru] using h
  have h2 : reflOf Q v hv * reflOf Q u hu = reflOf Q u hu * reflOf Q v hv := by
    calc reflOf Q v hv * reflOf Q u hu
        = reflOf Q v hv * reflOf Q u hu * ((reflOf Q v hv)⁻¹ * reflOf Q v hv) := by group
      _ = (reflOf Q v hv * reflOf Q u hu * (reflOf Q v hv)⁻¹) * reflOf Q v hv := by group
      _ = reflOf Q u hu * reflOf Q v hv := by rw [h']
  exact h2.symm

end CFSG.OddStandard.SmallF3.Omega
