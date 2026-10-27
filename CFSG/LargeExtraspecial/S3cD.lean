module

public import CFSG.LargeExtraspecial.S3cShult

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def Dbar (g : G) : Subgroup S.O :=
  S.Lbar g ⊓ (pointRadical S.q (S.cl (g * S.z * g⁻¹))).comap S.O.subtype

theorem card_Dbar_le_four {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) : Nat.card (S.Dbar g) ≤ 4 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨s₁, hs₁, hs₁'⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Dbar g) {1}
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨s₂, hs₂, hs₂'⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Dbar g) {1, s₁}
    (Finset.card_le_two.trans_lt (by omega))
  obtain ⟨s₃, hs₃, hs₃'⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Dbar g)
    {1, s₁, s₂, s₁ * s₂} (Finset.card_le_four.trans_lt h)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs₁' hs₂' hs₃'
  have hsq : ∀ s ∈ S.Dbar g, s * s = 1 := fun s hs => by
    have := S.sq_eq_one_of_mem_Lbar haQ hs.1
    rwa [pow_two] at this
  have hinv : ∀ s ∈ S.Dbar g, ∀ t, s * t = 1 → t = s := fun s hs t hst => by
    calc t = s * s * t := by rw [hsq s hs, one_mul]
      _ = s := by rw [mul_assoc, hst, mul_one]
  have hne1 : ∀ t : S.O, t ≠ 1 → (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun t ht h => ht (Subtype.ext h)
  refine S.false_of_three_mem_pointRadical haQ hne hno (S.coe_mem_LbarLin hs₁.1)
    (S.coe_mem_LbarLin hs₂.1) (S.coe_mem_LbarLin hs₃.1) hs₁.2 hs₂.2 hs₃.2 (hne1 _ hs₁')
    (hne1 _ hs₂'.1) (hne1 _ hs₃'.1) ?_ ?_ ?_ ?_
  · rw [← Subgroup.coe_mul]
    exact hne1 _ fun h' => hs₂'.2 (hinv s₁ hs₁ s₂ h')
  · rw [← Subgroup.coe_mul]
    exact hne1 _ fun h' => hs₃'.2.1 (hinv s₁ hs₁ s₃ h')
  · rw [← Subgroup.coe_mul]
    exact hne1 _ fun h' => hs₃'.2.2.1 (hinv s₂ hs₂ s₃ h')
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    exact hne1 _ fun h' => hs₃'.2.2.2 (hinv (s₁ * s₂) (mul_mem hs₁ hs₂) s₃ h')

theorem conj_mem_Dbar_of_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {m : S.O} (hmM : m ∈ S.Mbar)
    (hma : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    {s : S.O} (hs : s ∈ S.Dbar g) : m * s * m⁻¹ ∈ S.Dbar g := by
  obtain ⟨⟨h, hh⟩, rfl⟩ := MonoidHom.mem_range.mp hmM
  have hL := S.Lbar_mul_eq_of_fix haQ hne hh hma
  refine ⟨?_, ?_⟩
  · rw [← hL, S.Lbar_mul hh]
    exact ⟨s, hs.1, rfl⟩
  · show ((S.ρ ⟨h, hh⟩ * s * (S.ρ ⟨h, hh⟩)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈
      pointRadical S.q (S.cl (g * S.z * g⁻¹))
    have := conj_mem_pointRadical (m := ((S.ρ ⟨h, hh⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (S.ρ ⟨h, hh⟩).2 hs.2
    rw [hma] at this
    simpa using this

end Setting

end CFSG.LargeExtraspecial
