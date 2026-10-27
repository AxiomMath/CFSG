module

public import Mathlib.GroupTheory.Sylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

variable {G : Type*} [Group G] [Finite G]

theorem subgroup_index_in_normal_sup (R P : Subgroup G) [R.Normal] :
    (P.subgroupOf (R ⊔ P)).index = (P.subgroupOf R).index := by
  change P.relIndex (R ⊔ P) = P.relIndex R
  have hP := Subgroup.relIndex_mul_relIndex (P ⊓ R) P (R ⊔ P)
    inf_le_left le_sup_right
  have hR := Subgroup.relIndex_mul_relIndex (P ⊓ R) R (R ⊔ P)
    inf_le_right le_sup_left
  rw [Subgroup.inf_relIndex_left] at hP
  rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_sup_left] at hR
  apply Nat.eq_of_mul_eq_mul_left
    (show 0 < R.relIndex P from
      Nat.card_pos (α := P ⧸ R.subgroupOf P))
  exact hP.trans (hR.symm.trans (Nat.mul_comm _ _))

theorem sylow_in_normal_sup_of_sylow_intersection
    {p : ℕ} (hp : p.Prime) (R P : Subgroup G) [R.Normal]
    (hP : IsPGroup p P)
    (hintersection : ∃ T : Sylow p R,
      (T : Subgroup R).map R.subtype = P ⊓ R) :
    ∃ Q : Sylow p (R ⊔ P : Subgroup G),
      (Q : Subgroup (R ⊔ P : Subgroup G)) = P.subgroupOf (R ⊔ P) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hT⟩ := hintersection
  have hTint : (T : Subgroup R) = P.subgroupOf R := by
    apply Subgroup.map_injective (f := R.subtype) R.subtype_injective
    rw [hT, Subgroup.subgroupOf_map_subtype]
  have hindex : ¬ p ∣ (P.subgroupOf (R ⊔ P)).index := by
    rw [subgroup_index_in_normal_sup R P, ← hTint]
    exact T.not_dvd_index
  have hinternal : IsPGroup p (P.subgroupOf (R ⊔ P)) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : P ≤ R ⊔ P)).symm
  exact ⟨hinternal.toSylow hindex, IsPGroup.toSylow_coe hinternal hindex⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
