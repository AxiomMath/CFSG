module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3OddCoreAll

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

open CFSG.ComponentClassification.CatalogueBOddQuadratic in
theorem exists_hypPair_and_aniso [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V) :
    ∃ (P : HypPair Q) (a : V), a ∈ P.perp ∧ Q a ≠ 0 := by
  have hodd3 : Odd (Nat.card K) := by rw [hK]; decide
  have hA : HasAnisoPerp Q := hasAnisoPerp_of_three_le_finrank hQ hdim
  obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_three_le hodd3 Q hQ hdim
  obtain ⟨P, -⟩ := exists_hypPair hQ hvQ hv0
  obtain ⟨a, ha, hc⟩ := hA P
  exact ⟨P, a, ha, hc⟩

theorem mem_scalars_of_mem_center [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V)
    {z : ↥(elementaryGroup Q)} (hz : z ∈ Subgroup.center ↥(elementaryGroup Q)) :
    (z : V ≃ₗ[K] V) ∈ scalars K V := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  obtain ⟨P, a, -, -⟩ := exists_hypPair_and_aniso hK hQ hdim
  have hA : HasAnisoPerp Q := hasAnisoPerp_of_three_le_finrank hQ hdim
  exact mem_scalars_of_commute_eichler h2 hQ hA P (elementaryGroup_le_orthogonalGroup Q z.2)
    fun u w _ _ => (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz ⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩)).symm

theorem mem_center_of_mem_scalars {z : ↥(elementaryGroup Q)}
    (hz : (z : V ≃ₗ[K] V) ∈ scalars K V) : z ∈ Subgroup.center ↥(elementaryGroup Q) :=
  Subgroup.mem_center_iff.mpr fun g => Subtype.ext (commute_of_mem_scalars hz g).symm

theorem mem_center_iff_mem_scalars [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V)
    {z : ↥(elementaryGroup Q)} :
    z ∈ Subgroup.center ↥(elementaryGroup Q) ↔ (z : V ≃ₗ[K] V) ∈ scalars K V :=
  ⟨mem_scalars_of_mem_center hK hQ hdim, mem_center_of_mem_scalars⟩

theorem isPGroup_center_elementaryGroup [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V) :
    IsPGroup 2 (Subgroup.center ↥(elementaryGroup Q)) := by
  obtain ⟨P, a, -, ha⟩ := exists_hypPair_and_aniso hK hQ hdim
  intro z
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  have hs := mem_scalars_of_mem_center hK hQ hdim z.2
  have := mul_self_eq_one_of_mem_scalars (elementaryGroup_le_orthogonalGroup Q z.1.2) hs ha
  rw [pow_one, pow_two]
  exact this

end CFSG.ClassicalGroups.Orthogonal.Small
