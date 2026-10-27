module

public import CFSG.LargeExtraspecial.GLRElimCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

namespace Levi

variable (Λ : Levi C)

theorem mul_self_ne_one {σ : G} (hσM : σ ∈ S.M) (hσX : σ ∉ C.X) (hσL : Λ.Normalizes σ)
    (hσz : σ * σ = S.z) {y : G} (hyM : y ∈ S.M) (hyX : y ∉ C.X) : y * y ≠ 1 := by
  intro hyy
  obtain ⟨q, hq, hqL⟩ := Λ.exists_normalizes_mul hyM
  have hy₀M : q * y ∈ S.M := S.M.mul_mem (S.QG_le_M hq) hyM
  have hy₀X : q * y ∉ C.X := fun h => hyX (by
    have := C.X.mul_mem (C.X.inv_mem (C.QG_le_X hq)) h
    rwa [inv_mul_cancel_left] at this)
  have hσinvX : σ⁻¹ ∉ C.X := fun h => hσX (by simpa using C.X.inv_mem h)
  have hX : σ⁻¹ * (q * y) ∈ C.X := C.mul_mem_X_of_not_mem (S.M.inv_mem hσM) hy₀M hσinvX hy₀X
  obtain ⟨l, hl, hl'⟩ := Λ.exists_eq_of_normalizes hX (hσL.inv.mul hqL)
  have hlM := Λ.L_le_M hl
  have hwM : σ * l ∈ S.M := S.M.mul_mem hσM hlM
  have hsq : (q * y) * (q * y) = (σ * l) * (σ * l) := by
    rcases hl' with h | h
    · rw [show q * y = σ * l by rw [← h]; group]
    · have e : q * y = σ * l * S.z := by
        rw [show q * y = σ * (S.z * l) by rw [← h]; group, ← S.z_comm hlM]
        group
      rw [e]
      calc σ * l * S.z * (σ * l * S.z) = σ * l * (S.z * (σ * l)) * S.z := by group
        _ = σ * l * (σ * l * S.z) * S.z := by rw [S.z_comm hwM]
        _ = σ * l * (σ * l) * (S.z * S.z) := by group
        _ = σ * l * (σ * l) := by rw [S.z_mul_z, mul_one]
  have hl₂ : σ⁻¹ * l * σ * l ∈ Λ.L := Λ.L.mul_mem (hσL.inv_conj_mem hl) hl
  have hww : (σ * l) * (σ * l) = S.z * (σ⁻¹ * l * σ * l) := by
    rw [← hσz]
    group
  have hp : q⁻¹ * ((q * y) * q⁻¹ * (q * y)⁻¹) ∈ S.QG :=
    S.QG.mul_mem (S.QG.inv_mem hq) (S.conj_mem_QG hy₀M (S.QG.inv_mem hq))
  have hyy' : y * y = (q⁻¹ * ((q * y) * q⁻¹ * (q * y)⁻¹)) * S.z * (σ⁻¹ * l * σ * l) := by
    rw [mul_assoc _ S.z, ← hww, ← hsq]
    group
  rw [hyy] at hyy'
  have hl₁ : σ⁻¹ * l * σ * l = 1 := by
    refine Λ.eq_one_of_mem_QG _ hl₂ ?_
    have e : σ⁻¹ * l * σ * l = ((q⁻¹ * ((q * y) * q⁻¹ * (q * y)⁻¹)) * S.z)⁻¹ :=
      eq_inv_of_mul_eq_one_right hyy'.symm
    rw [e]
    exact S.QG.inv_mem (S.QG.mul_mem hp S.z_mem_QG)
  rw [hl₁, mul_one] at hyy' hww
  have hy₀z : (q * y) * (q * y) = S.z := by rw [hsq, hww]
  have hpz : q⁻¹ * ((q * y) * q⁻¹ * (q * y)⁻¹) = S.z := by
    rw [eq_inv_of_mul_eq_one_left hyy'.symm, S.z_inv]
  exact Config.mul_conj_ne_z hy₀M hy₀X (Or.inr hy₀z) (S.QG.inv_mem hq) hpz

end Levi

end CFSG.LargeExtraspecial.GLR
