module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem fx_qe_q8_images {G P : Type} [Group G] [Group P] {L Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ≤ L)
    (hQ₂ : Q₂ ≤ L) (e₁ : ↥Q₁ ≃* QuaternionGroup 2) (e₂ : ↥Q₂ ≃* QuaternionGroup 2)
    (hc : ⁅Q₁, Q₂⁆ = ⊥) {z : G} (hz₁ : z ∈ Q₁) (hz₂ : z ∈ Q₂)
    (he₁ : e₁ ⟨z, hz₁⟩ = QuaternionGroup.a 2) (he₂ : e₂ ⟨z, hz₂⟩ = QuaternionGroup.a 2)
    (φ : ↥L →* P) :
    ∃ q r s : P, q * q = φ ⟨z, hQ₁ hz₁⟩ ∧ r * r = φ ⟨z, hQ₁ hz₁⟩ ∧ s * s = φ ⟨z, hQ₁ hz₁⟩ ∧
      r * q = q⁻¹ * r ∧ s * q = q * s ∧ s * r = r * s := by
  have haa : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by
    rw [QuaternionGroup.a_mul_a]
    congr 1
  have hxx : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 := by
    rw [QuaternionGroup.xa_mul_xa]
    congr 1
  have hxa : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      (QuaternionGroup.a 1)⁻¹ * QuaternionGroup.xa 0 := by
    have hinv : (QuaternionGroup.a 1 : QuaternionGroup 2)⁻¹ = QuaternionGroup.a (-1) := rfl
    rw [hinv, QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
    congr 1
  let ι₁ : ↥Q₁ →* ↥L := Subgroup.inclusion hQ₁
  let ι₂ : ↥Q₂ →* ↥L := Subgroup.inclusion hQ₂
  let i₁ : ↥Q₁ := e₁.symm (QuaternionGroup.a 1)
  let j₁ : ↥Q₁ := e₁.symm (QuaternionGroup.xa 0)
  let i₂ : ↥Q₂ := e₂.symm (QuaternionGroup.a 1)
  have hii : i₁ * i₁ = ⟨z, hz₁⟩ := by
    apply e₁.injective
    rw [map_mul e₁ i₁ i₁, he₁]
    simp only [i₁, MulEquiv.apply_symm_apply]
    exact haa
  have hjj : j₁ * j₁ = ⟨z, hz₁⟩ := by
    apply e₁.injective
    rw [map_mul e₁ j₁ j₁, he₁]
    simp only [j₁, MulEquiv.apply_symm_apply]
    exact hxx
  have hii2 : i₂ * i₂ = ⟨z, hz₂⟩ := by
    apply e₂.injective
    rw [map_mul e₂ i₂ i₂, he₂]
    simp only [i₂, MulEquiv.apply_symm_apply]
    exact haa
  have hji : j₁ * i₁ = i₁⁻¹ * j₁ := by
    apply e₁.injective
    rw [map_mul e₁ j₁ i₁, map_mul e₁ i₁⁻¹ j₁, map_inv e₁ i₁]
    simp only [i₁, j₁, MulEquiv.apply_symm_apply]
    exact hxa
  have hcomm : ∀ (x : ↥Q₁) (y : ↥Q₂), ((x : G) * (y : G) = (y : G) * (x : G)) := by
    intro x y
    have hx : (x : G) ∈ Subgroup.centralizer (Q₂ : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc) x.2
    exact ((Subgroup.mem_centralizer_iff.mp hx) y y.2).symm
  have hq2 : ι₁ i₁ * ι₁ i₁ = ⟨z, hQ₁ hz₁⟩ := by
    rw [← map_mul ι₁ i₁ i₁, hii]
    rfl
  have hr2 : ι₁ j₁ * ι₁ j₁ = ⟨z, hQ₁ hz₁⟩ := by
    rw [← map_mul ι₁ j₁ j₁, hjj]
    rfl
  have hs2 : ι₂ i₂ * ι₂ i₂ = ⟨z, hQ₁ hz₁⟩ := by
    rw [← map_mul ι₂ i₂ i₂, hii2]
    exact Subtype.ext rfl
  have h4 : ι₁ j₁ * ι₁ i₁ = (ι₁ i₁)⁻¹ * ι₁ j₁ := by
    calc ι₁ j₁ * ι₁ i₁ = ι₁ (j₁ * i₁) := (map_mul ι₁ j₁ i₁).symm
      _ = ι₁ (i₁⁻¹ * j₁) := by rw [hji]
      _ = ι₁ (i₁⁻¹) * ι₁ j₁ := map_mul ι₁ (i₁⁻¹) j₁
      _ = (ι₁ i₁)⁻¹ * ι₁ j₁ := by rw [map_inv ι₁ i₁]
  refine ⟨φ (ι₁ i₁), φ (ι₁ j₁), φ (ι₂ i₂), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul φ (ι₁ i₁) (ι₁ i₁), hq2]
  · rw [← map_mul φ (ι₁ j₁) (ι₁ j₁), hr2]
  · rw [← map_mul φ (ι₂ i₂) (ι₂ i₂), hs2]
  · rw [← map_mul φ (ι₁ j₁) (ι₁ i₁), h4, map_mul φ ((ι₁ i₁)⁻¹) (ι₁ j₁),
      map_inv φ (ι₁ i₁)]
  · rw [← map_mul φ (ι₂ i₂) (ι₁ i₁), ← map_mul φ (ι₁ i₁) (ι₂ i₂)]
    congr 1
    apply Subtype.ext
    change (i₂ : G) * (i₁ : G) = (i₁ : G) * (i₂ : G)
    exact (hcomm i₁ i₂).symm
  · rw [← map_mul φ (ι₂ i₂) (ι₁ j₁), ← map_mul φ (ι₁ j₁) (ι₂ i₂)]
    congr 1
    apply Subtype.ext
    change (i₂ : G) * (j₁ : G) = (j₁ : G) * (i₂ : G)
    exact (hcomm j₁ i₂).symm

end CFSG.OddStandard.SmallF3.Omega
