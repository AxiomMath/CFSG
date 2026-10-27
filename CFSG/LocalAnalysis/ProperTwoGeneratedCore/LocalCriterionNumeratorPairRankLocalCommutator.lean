module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorDecomposition
public import CFSG.GroupTheory.InvolutiveAutomorphismInversion

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG
open CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

universe u v

variable {A : Type u} [Group A]
variable {I : Type v} [Group I] [Finite I] [MulDistribMulAction A I]

theorem odd_local_inversion_subgroup_eq_commutator
    (hodd : Odd (Nat.card I)) (b : A) (hb : b * b = 1)
    (J : Subgroup I) [CFSG.IsInvariant A I J]
    (K : Subgroup I)
    (hK : ∀ x : I, x ∈ K ↔ x ∈ J ∧ b • x = x⁻¹) :
    K = actorCommutatorSubgroup b J ∧ (K.subgroupOf J).Normal := by
  have hcomm : K = actorCommutatorSubgroup b J := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxJ, hxanti⟩ := (hK x).mp hx
      exact odd_inverted_element_mem_commutator hodd b J x hxJ hxanti
    · apply (actorCommutatorSubgroup_le b J K).mpr
      intro x hx
      obtain ⟨c, hc, r, hr, hcf, hra, hprod⟩ :=
        odd_involution_fixed_inverted_decomposition hodd b hb J x hx
      have hrK : r ∈ K := (hK r).mpr ⟨hr, hra⟩
      have hgen : x⁻¹ * (b • x) = r⁻¹ * r⁻¹ := by
        rw [hprod, smul_mul', hcf, hra]
        group
      rw [hgen]
      exact K.mul_mem (K.inv_mem hrK) (K.inv_mem hrK)
  let alpha : MulAut J := MulDistribMulAction.toMulAut A J b
  have halpha : alpha * alpha = 1 := by
    calc
      alpha * alpha = (MulDistribMulAction.toMulAut A J) (b * b) :=
        (map_mul (MulDistribMulAction.toMulAut A J) b b).symm
      _ = 1 := by rw [hb, map_one]
  have hJodd : Odd (Nat.card J) := hodd.of_dvd_nat J.card_subgroup_dvd_card
  have hset : (K.subgroupOf J : Set J) = {x : J | alpha x = x⁻¹} := by
    ext x
    change (x : I) ∈ K ↔ alpha x = x⁻¹
    rw [hK]
    constructor
    · intro hx
      exact Subtype.ext hx.2
    · intro hx
      exact ⟨x.property, congrArg Subtype.val hx⟩
  have hnative := OddInversion.inversion_set_conjugacy_and_normality hJodd alpha halpha
  have hinvariant := hnative.2.1.mp ⟨K.subgroupOf J, hset⟩
  obtain ⟨N, hNset, hNnormal, _hNcomm⟩ := hnative.2.2 hinvariant
  have hKN : K.subgroupOf J = N := SetLike.coe_injective (hset.trans hNset.symm)
  exact ⟨hcomm, hKN.symm ▸ hNnormal⟩

theorem odd_local_cyclic_inversion_subgroup_eq_commutator
    (hodd : Odd (Nat.card I)) (b : A) (hb : b * b = 1)
    (J : Subgroup I) [CFSG.IsInvariant A I J]
    (K : Subgroup I) (hcyclic : IsCyclic K)
    (hK : ∀ x : I, x ∈ K ↔ x ∈ J ∧ b • x = x⁻¹) :
    K = actorCommutatorSubgroup b J ∧ (K.subgroupOf J).Normal ∧
      IsCyclic (actorCommutatorSubgroup b J) := by
  obtain ⟨heq, hnormal⟩ := odd_local_inversion_subgroup_eq_commutator hodd b hb J K hK
  exact ⟨heq, hnormal, heq ▸ hcyclic⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
