module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorRelative
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorProduct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorGeometry
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open CFSG

universe u v

variable {A : Type u} [Group A] [Finite A]
variable {I : Type v} [Group I] [Finite I] [MulDistribMulAction A I]

theorem odd_four_group_two_centralizer_commutator_generation [IsKleinFour A]
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hodd : Odd (Nat.card I)) :
    actorCommutatorSubgroup b (⊤ : Subgroup I) =
      actorCommutatorSubgroup b (actorFixedSubgroup (I := I) a) ⊔
        actorCommutatorSubgroup b (actorFixedSubgroup (I := I) (a * b)) := by
  let : IsMulCommutative A := IsKleinFour.isMulCommutative
  let Ca := actorFixedSubgroup (I := I) a
  let Cb := actorFixedSubgroup (I := I) b
  let Cab := actorFixedSubgroup (I := I) (a * b)
  let E := fixedPointSubgroup A I
  let R := actorCommutatorSubgroup b Ca
  let S := actorCommutatorSubgroup b Cab
  let K : Subgroup I := R ⊔ S
  let : CFSG.IsInvariant A I Ca := actorFixedSubgroup_invariant a
  let : CFSG.IsInvariant A I Cab := actorFixedSubgroup_invariant (a * b)
  let : CFSG.IsInvariant A I R := actorCommutatorSubgroup_invariant b Ca
  let : CFSG.IsInvariant A I S := actorCommutatorSubgroup_invariant b Cab
  let : CFSG.IsInvariant A I K := isInvariant_sup R S
  have hEa : E ≤ Ca := fun _ hx => hx a
  have hEab : E ≤ Cab := fun _ hx => hx (a * b)
  have hcover := four_group_two_fixed_covers (I := I) a b ha hb hab hodd
  change (∀ x ∈ Ca, ∃ c ∈ E, ∃ r ∈ K, x = c * r) ∧
    (∀ x ∈ Cab, ∃ c ∈ E, ∃ r ∈ K, x = c * r) at hcover
  have hia : K.relIndex Ca = K.relIndex E :=
    relative_index_eq_of_product_cover K E Ca hEa hcover.1
  have hiab : K.relIndex Cab = K.relIndex E :=
    relative_index_eq_of_product_cover K E Cab hEab hcover.2
  have hrel := four_group_relative_index_identity a b ha hb hab hodd K
  change K.index * (K.relIndex E) ^ 2 =
    K.relIndex Ca * K.relIndex Cb * K.relIndex Cab at hrel
  rw [hia, hiab] at hrel
  have hpos : 0 < K.relIndex E := by
    change 0 < Nat.card (E ⧸ K.subgroupOf E)
    exact Nat.card_pos
  have hindex : K.index = K.relIndex Cb := by
    apply Nat.mul_right_cancel (m := (K.relIndex E) ^ 2)
      (pow_pos hpos 2)
    calc
      _ = K.relIndex E * K.relIndex Cb * K.relIndex E := hrel
      _ = _ := by ring
  change actorCommutatorSubgroup b (⊤ : Subgroup I) = K
  apply le_antisymm
  · apply (actorCommutatorSubgroup_le b ⊤ K).2
    intro x _
    obtain ⟨c, hc, k, hk, hx⟩ := subgroup_product_cover_of_index_eq K Cb hindex x
    have hcf : b • c = c := hc
    have hbk : b • k ∈ K :=
      (CFSG.IsInvariant.invariant (A := A) (G := I) (H := K) b k).1 hk
    rw [hx]
    simpa only [mul_inv_rev, smul_mul', hcf, mul_assoc, inv_mul_cancel_left] using
      K.mul_mem (K.inv_mem hk) hbk
  · apply sup_le
    · exact actorCommutatorSubgroup_mono b le_top
    · exact actorCommutatorSubgroup_mono b le_top

theorem odd_elementary_four_group_two_centralizer_commutator_generation
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 4)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hodd : Odd (Nat.card I)) :
    actorCommutatorSubgroup b (⊤ : Subgroup I) =
      actorCommutatorSubgroup b (actorFixedSubgroup (I := I) a) ⊔
        actorCommutatorSubgroup b (actorFixedSubgroup (I := I) (a * b)) := by
  let : IsKleinFour A := isKleinFour_of_elementary_card_four hcard
  exact odd_four_group_two_centralizer_commutator_generation a b ha hb hab hodd

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
