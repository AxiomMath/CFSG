module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

universe u

variable {G : Type u} [Group G]

theorem abelianization_eq_one_of_conjugate_product (z a b : G)
    (ha : IsConj z a) (hb : IsConj z b) (hab : IsConj z (a * b)) :
    Abelianization.of z = 1 := by
  have ha' := isConj_iff_eq.mp (Abelianization.of.map_isConj ha)
  have hb' := isConj_iff_eq.mp (Abelianization.of.map_isConj hb)
  have hab' := isConj_iff_eq.mp (Abelianization.of.map_isConj hab)
  have heq : Abelianization.of z * Abelianization.of z = Abelianization.of z := by
    calc
      Abelianization.of z * Abelianization.of z =
          Abelianization.of a * Abelianization.of b := congrArg₂ (· * ·) ha' hb'
      _ = Abelianization.of (a * b) := (map_mul _ a b).symm
      _ = Abelianization.of z := hab'.symm
  exact mul_left_cancel (heq.trans (mul_one _).symm)

theorem single_class_generated_group_isPerfect (z a b : G)
    (hgen : Subgroup.closure (conjugatesOf z) = ⊤)
    (ha : IsConj z a) (hb : IsConj z b) (hab : IsConj z (a * b)) :
    Group.IsPerfect G := by
  have hz := abelianization_eq_one_of_conjugate_product z a b ha hb hab
  have hclass : conjugatesOf z ⊆ (Abelianization.of : G →* Abelianization G).ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    exact (isConj_iff_eq.mp (Abelianization.of.map_isConj hx)).symm.trans hz
  have hle := (Subgroup.closure_le _).mpr hclass
  rw [hgen, Abelianization.ker_of] at hle
  exact ⟨top_le_iff.mp hle⟩

theorem four_group_has_distinct_nonidentity (W : Subgroup G) [IsKleinFour W] :
    ∃ a b : W, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  let : Finite W := IsKleinFour.instFinite
  have hexists (a : W) : ∃ b : W, b ≠ 1 ∧ b ≠ a := by
    by_contra hnone
    push Not at hnone
    have hcases : ∀ b : W, b = 1 ∨ b = a := by
      intro b
      by_cases hb : b = 1
      · exact Or.inl hb
      · exact Or.inr (hnone b hb)
    let f : W → ({(1 : W), a} : Set W) := fun b => ⟨b, hcases b⟩
    have hf : Function.Injective f := by
      intro b c hbc
      exact congrArg Subtype.val hbc
    have htwo : Nat.card ({(1 : W), a} : Set W) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      by_cases ha : a = 1
      · simp [ha]
      · exact (Set.ncard_pair (Ne.symm ha)).le
    have hbound := (Nat.card_le_card_of_injective f hf).trans htwo
    rw [IsKleinFour.card_four] at hbound
    omega
  obtain ⟨a, ha, _⟩ := hexists 1
  obtain ⟨b, hb, hba⟩ := hexists a
  exact ⟨a, b, ha, hb, hba.symm⟩

theorem single_involution_class_four_group_isPerfect (z : G)
    (hclass : ∀ x : G, orderOf x = 2 → IsConj z x)
    (hgen : Subgroup.closure (conjugatesOf z) = ⊤)
    (W : Subgroup G) [IsKleinFour W] : Group.IsPerfect G := by
  obtain ⟨a, b, ha, hb, hab⟩ := four_group_has_distinct_nonidentity W
  have horder (x : W) (hx : x ≠ 1) : orderOf (x : G) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    constructor
    · simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
        congrArg Subtype.val (IsKleinFour.mul_self x)
    · intro heq
      exact hx (Subtype.ext heq)
  have habone : a * b ≠ 1 := by
    intro heq
    have heq' := mul_eq_one_iff_eq_inv.mp heq
    rw [IsKleinFour.inv_eq_self] at heq'
    exact hab heq'
  exact single_class_generated_group_isPerfect z a b hgen
    (hclass a (horder a ha)) (hclass b (horder b hb))
    (by simpa only [Subgroup.coe_mul] using hclass (a * b) (horder (a * b) habone))

end CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction
