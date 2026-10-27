module

public import CFSG.CharacterTheory.Wreathed.CentralProductAutomorphism

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def vQuotientQuaternionProjection (l : ℕ) :
    QuaternionGroup 2 →* vSubgroup l ⧸ Subgroup.center (vSubgroup l) :=
  (QuotientGroup.mk' (Subgroup.center (vSubgroup l))).comp (quaternionToV l)

theorem vQuotientQuaternionProjection_eq_one_iff (l : ℕ) (hl : 0 < l)
    (q : QuaternionGroup 2) :
    vQuotientQuaternionProjection l q = 1 ↔ q = 1 ∨ q = QuaternionGroup.a 2 := by
  change QuotientGroup.mk' (Subgroup.center (vSubgroup l)) (quaternionToV l q) = 1 ↔ _
  change ((quaternionToV l q : vSubgroup l) :
    vSubgroup l ⧸ Subgroup.center (vSubgroup l)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, v_mem_center_iff l hl]
  exact quaternionEight_mem_center_iff l hl q

theorem vQuotientQuaternionProjection_surjective (l : ℕ) (hl : 0 < l) :
    Function.Surjective (vQuotientQuaternionProjection l) := by
  intro g
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (vSubgroup l)) g
  obtain ⟨⟨c, q⟩, rfl⟩ := centralProductToV_surjective l hl v
  refine ⟨q, ?_⟩
  have hmul : centralProductToV l hl (c, q) =
      centralProductToV l hl (c, 1) * quaternionToV l q := by
    apply Subtype.ext
    change diagonalHom (4 * l) c * quaternionEightEmbedding l q =
      (diagonalHom (4 * l) c * quaternionEightEmbedding l 1) * quaternionEightEmbedding l q
    rw [map_one, mul_one]
  have hcentral : centralProductToV l hl (c, 1) ∈ Subgroup.center (vSubgroup l) := by
    rw [v_mem_center_iff l hl]
    exact centralProduct_central_of_central_quaternion l hl c 1 (Or.inl rfl)
  have hz : QuotientGroup.mk' (Subgroup.center (vSubgroup l))
      (centralProductToV l hl (c, 1)) = 1 := (QuotientGroup.eq_one_iff _).mpr hcentral
  rw [hmul, map_mul, hz, one_mul]
  rfl

theorem vQuotientQuaternionProjection_eq_iff (l : ℕ) (hl : 0 < l)
    (q r : QuaternionGroup 2) :
    vQuotientQuaternionProjection l q = vQuotientQuaternionProjection l r ↔
      q / r = 1 ∨ q / r = QuaternionGroup.a 2 := by
  rw [← div_eq_one, ← (vQuotientQuaternionProjection l).map_div,
    vQuotientQuaternionProjection_eq_one_iff l hl]

theorem v_quotient_three_nonzero (l : ℕ) (hl : 0 < l)
    (g : vSubgroup l ⧸ Subgroup.center (vSubgroup l)) :
    g = 1 ∨ g = vQuotientQuaternionProjection l (QuaternionGroup.a 1) ∨
      g = vQuotientQuaternionProjection l (QuaternionGroup.xa 0) ∨
      g = vQuotientQuaternionProjection l (QuaternionGroup.xa 3) := by
  obtain ⟨q, rfl⟩ := vQuotientQuaternionProjection_surjective l hl g
  have hcases : q = 1 ∨
      (q / QuaternionGroup.a 1 = 1 ∨ q / QuaternionGroup.a 1 = QuaternionGroup.a 2) ∨
      (q / QuaternionGroup.xa 0 = 1 ∨ q / QuaternionGroup.xa 0 = QuaternionGroup.a 2) ∨
      (q / QuaternionGroup.xa 3 = 1 ∨ q / QuaternionGroup.xa 3 = QuaternionGroup.a 2) ∨
      q = QuaternionGroup.a 2 :=
    (show ∀ q : QuaternionGroup 2, q = 1 ∨
      (q / QuaternionGroup.a 1 = 1 ∨ q / QuaternionGroup.a 1 = QuaternionGroup.a 2) ∨
      (q / QuaternionGroup.xa 0 = 1 ∨ q / QuaternionGroup.xa 0 = QuaternionGroup.a 2) ∨
      (q / QuaternionGroup.xa 3 = 1 ∨ q / QuaternionGroup.xa 3 = QuaternionGroup.a 2) ∨
      q = QuaternionGroup.a 2 by decide) q
  rcases hcases with h | h | h | h | h
  · exact Or.inl ((vQuotientQuaternionProjection_eq_one_iff l hl q).mpr (Or.inl h))
  · exact Or.inr (Or.inl ((vQuotientQuaternionProjection_eq_iff l hl _ _).mpr h))
  · exact Or.inr (Or.inr (Or.inl ((vQuotientQuaternionProjection_eq_iff l hl _ _).mpr h)))
  · exact Or.inr (Or.inr (Or.inr ((vQuotientQuaternionProjection_eq_iff l hl _ _).mpr h)))
  · exact Or.inl ((vQuotientQuaternionProjection_eq_one_iff l hl q).mpr (Or.inr h))

theorem v_quotient_representatives_distinct (l : ℕ) (hl : 0 < l) :
    vQuotientQuaternionProjection l (QuaternionGroup.a 1) ≠ 1 ∧
    vQuotientQuaternionProjection l (QuaternionGroup.xa 0) ≠ 1 ∧
    vQuotientQuaternionProjection l (QuaternionGroup.xa 3) ≠ 1 ∧
    vQuotientQuaternionProjection l (QuaternionGroup.a 1) ≠
      vQuotientQuaternionProjection l (QuaternionGroup.xa 0) ∧
    vQuotientQuaternionProjection l (QuaternionGroup.a 1) ≠
      vQuotientQuaternionProjection l (QuaternionGroup.xa 3) ∧
    vQuotientQuaternionProjection l (QuaternionGroup.xa 0) ≠
      vQuotientQuaternionProjection l (QuaternionGroup.xa 3) := by
  simp only [ne_eq, vQuotientQuaternionProjection_eq_one_iff l hl,
    vQuotientQuaternionProjection_eq_iff l hl]
  decide

@[expose] def vCycleQuotient (l : ℕ) (hl : 0 < l) :
    MulAut (vSubgroup l ⧸ Subgroup.center (vSubgroup l)) :=
  QuotientGroup.congr (Subgroup.center (vSubgroup l)) (Subgroup.center (vSubgroup l))
    (vCycle l hl) (by
      change (Subgroup.center (vSubgroup l)).map (vCycle l hl).toMonoidHom = _
      exact Subgroup.characteristic_iff_map_eq.mp inferInstance (vCycle l hl))

theorem vCycleQuotient_quaternion (l : ℕ) (hl : 0 < l) (q : QuaternionGroup 2) :
    vCycleQuotient l hl (vQuotientQuaternionProjection l q) =
      vQuotientQuaternionProjection l (quaternionCycle q) := by
  change QuotientGroup.congr _ _ _ _
    ((quaternionToV l q : vSubgroup l) :
      vSubgroup l ⧸ Subgroup.center (vSubgroup l)) = _
  rw [QuotientGroup.congr_mk, vCycle_quaternion]
  rfl

theorem vCycleQuotient_cycles_three (l : ℕ) (hl : 0 < l) :
    vCycleQuotient l hl (vQuotientQuaternionProjection l (QuaternionGroup.a 1)) =
      vQuotientQuaternionProjection l (QuaternionGroup.xa 0) ∧
    vCycleQuotient l hl (vQuotientQuaternionProjection l (QuaternionGroup.xa 0)) =
      vQuotientQuaternionProjection l (QuaternionGroup.xa 3) ∧
    vCycleQuotient l hl (vQuotientQuaternionProjection l (QuaternionGroup.xa 3)) =
      vQuotientQuaternionProjection l (QuaternionGroup.a 1) := by
  simp only [vCycleQuotient_quaternion, quaternionCycle_a_one, quaternionCycle_xa_zero]
  have hlast : quaternionCycle (QuaternionGroup.xa 3) = QuaternionGroup.a 1 := by decide
  rw [hlast]
  simp

end CFSG.Wreathed
