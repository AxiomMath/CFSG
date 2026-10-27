module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG

open scoped commutatorElement

theorem le_of_perfect_of_le_sup_center {Y : Type*} [Group Y] {J P : Subgroup Y}
    (hJ : ⁅J, J⁆ = J) (hP : ⁅P, P⁆ = P) (hle : P ≤ J ⊔ Subgroup.center Y) : P ≤ J := by
  have hcomm : ⁅J ⊔ Subgroup.center Y, J ⊔ Subgroup.center Y⁆ ≤ ⁅J, J⁆ := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨j₁, hj₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hu
    obtain ⟨j₂, hj₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hv
    have h1 : z₁ * (j₂ * z₂) = (j₂ * z₂) * z₁ :=
      (Subgroup.mem_center_iff.1 hz₁ _).symm
    have h2 : z₂ * j₁⁻¹ = j₁⁻¹ * z₂ := (Subgroup.mem_center_iff.1 hz₂ _).symm
    have e : ⁅j₁ * z₁, j₂ * z₂⁆ = ⁅j₁, j₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc j₁ * z₁ * (j₂ * z₂) * (j₁ * z₁)⁻¹ * (j₂ * z₂)⁻¹
          = j₁ * (z₁ * (j₂ * z₂)) * z₁⁻¹ * j₁⁻¹ * z₂⁻¹ * j₂⁻¹ := by group
        _ = j₁ * j₂ * (z₂ * j₁⁻¹) * z₂⁻¹ * j₂⁻¹ := by rw [h1]; group
        _ = j₁ * j₂ * j₁⁻¹ * j₂⁻¹ := by rw [h2]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hj₁ hj₂
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅J ⊔ Subgroup.center Y, J ⊔ Subgroup.center Y⁆ := Subgroup.commutator_mono hle hle
    _ ≤ ⁅J, J⁆ := hcomm
    _ = J := hJ

end CFSG

end
