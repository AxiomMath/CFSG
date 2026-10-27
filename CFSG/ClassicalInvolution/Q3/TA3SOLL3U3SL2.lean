module

public import CFSG.ClassicalInvolution.Models.Transfer.Unitary
public import CFSG.GH74.GLS.LU.StdPairUni

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.Transfer CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open scoped MatrixGroups

variable {X : Type} [Group X] {K : Type} [Field K] [Finite K]

private theorem ne_one_of_map_eq_of_orderOf_eq_two {G : Type*} [Group G] (θ : G →* X) {z : G}
    {t : X} (hzt : θ z = t) (ht : orderOf t = 2) : z ≠ 1 := by
  rintro rfl
  rw [map_one] at hzt
  rw [← hzt, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem exists_isClassicalSL2_of_psl3 (hodd : Odd (Nat.card K))
    (e : X ≃* StatedProj (StatedSL 3 K)) {t : X} (ht : orderOf t = 2) :
    ∃ L : Subgroup X, IsClassicalSL2 K L t := by
  let θ : SL(3, K) →* X := e.symm.toMonoidHom.comp
    ((projectiveSpecialLinearGroupEquivStatedProj 3 K).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center SL(3, K))))
  have hsurj : Function.Surjective θ :=
    e.symm.surjective.comp ((projectiveSpecialLinearGroupEquivStatedProj 3 K).surjective.comp
      (QuotientGroup.mk'_surjective _))
  have hker : θ.ker ≤ Subgroup.center SL(3, K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simpa [θ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] using hx
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨z, hz, hzt⟩ := GH74.GLS.LU.exists_involution_lift θ hker
    GH74.GLS.LU.center_pow_three (MonoidHom.mem_range.mpr (hsurj t)) ht2
  have hz1 := ne_one_of_map_eq_of_orderOf_eq_two θ hzt ht
  exact ⟨_, IsLongRootImage.isClassicalSL2 hodd le_rfl hsurj hker (Or.inl (by norm_num))
    ⟨_, z, GH74.GLS.LU.isLongRootSL2_of_involution h2 hz hz1, rfl, hzt⟩⟩

theorem exists_isClassicalSL2_of_psu3 {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (e : X ≃* StatedProj (StatedSU 3 (p ^ f) K)) {t : X} (ht : orderOf t = 2) :
    ∃ L : Subgroup X, IsClassicalSL2 (fixedSubfield K p f) L t := by
  let θ : Su K p f 3 →* X := e.symm.toMonoidHom.comp
    ((QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K))).comp
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)).toMonoidHom)
  have hsurj : Function.Surjective θ :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3)).surjective)
  have hker : θ.ker ≤ Subgroup.center (Su K p f 3) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3) x ∈
        (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K) := by
      simpa [θ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] using hx
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx' (g : GL (Fin 3) K))
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨z, hz, hzt⟩ := GH74.GLS.LU.exists_involution_lift θ hker
    (GH74.GLS.LU.center_pow_three_su hK) (MonoidHom.mem_range.mpr (hsurj t)) ht2
  have hz1 := ne_one_of_map_eq_of_orderOf_eq_two θ hzt ht
  exact ⟨_, IsLongRootSU2Image.isClassicalSL2 hK hp hq le_rfl hsurj hker (Or.inl (by norm_num))
    ⟨_, z, GH74.GLS.LU.isLongRootSU2_of_involution hK hp hz hz1, rfl, hzt⟩⟩

end CFSG.ClassicalInvolution.Q3.TA3
