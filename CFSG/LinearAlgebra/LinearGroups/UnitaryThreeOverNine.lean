module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineSylow

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.Assembly.LowTwoRank

theorem unitary_three_over_nine_order_perfectness_and_wreath_Sylow_model {F : Type} [Field F]
    (hF : Nat.card F = 9) :
    let bar : F → F := fun c => c ^ 3
    let hform : (d : ℕ) → (Fin d → F) → (Fin d → F) → F := fun _ u v => ∑ j, bar (u j) * v j
    let U : (d : ℕ) → Set (GL (Fin d) F) := fun d =>
      {A | ((A : Matrix (Fin d) (Fin d) F).map bar)ᵀ * A = 1}
    (StatedSU 3 3 F : Set (GL (Fin 3) F)) =
      {A | A ∈ U 3 ∧ (A : Matrix (Fin 3) (Fin 3) F).det = 1} ∧
    {v : Fin 1 → F | hform 1 v v = 1}.ncard = 4 ∧
    {v : Fin 2 → F | hform 2 v v = 1}.ncard = 24 ∧
    {v : Fin 3 → F | hform 3 v v = 1}.ncard = 252 ∧
    (U 2).ncard = 96 ∧ (U 3).ncard = 24192 ∧ Nat.card (StatedSU 3 3 F) = 6048 ∧
    (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 3 F) = ⊥ ∧
    Group.IsPerfect (StatedSU 3 3 F) ∧ StatedClassicalModel (StatedSU 3 3 F) .PSU 3 3 1 ∧
    (∀ i : Fˣ, orderOf i = 4 →
      (∃ s t w : StatedSU 3 3 F,
        ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(i : F)⁻¹, (i : F), 1] ∧
        ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(i : F)⁻¹, 1, (i : F)] ∧
        ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 0, 1; 0, 1, 0]) ∧
      ∀ s t w : StatedSU 3 3 F,
        ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(i : F)⁻¹, (i : F), 1] →
        ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(i : F)⁻¹, 1, (i : F)] →
        ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 0, 1; 0, 1, 0] →
        s * t = t * s ∧ orderOf s = 4 ∧ orderOf t = 4 ∧
        Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥ ∧ orderOf w = 2 ∧
        w ∉ Subgroup.closure {s, t} ∧ w⁻¹ * s * w = t ∧ w⁻¹ * t * w = s ∧
        Nat.card (Subgroup.closure {s, t, w}) = 32 ∧
        (∃ P : Sylow 2 (StatedSU 3 3 F), (P : Subgroup (StatedSU 3 3 F)) =
          Subgroup.closure {s, t, w}) ∧
        ((((s * t) ^ 2 : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          diagonal ![1, -1, -1] ∧
        orderOf ((s * t) ^ 2) = 2 ∧ (s * t) ^ 2 ∈ Subgroup.closure {s, t, w} ∧
        ∀ g ∈ Subgroup.closure {s, t, w}, g * (s * t) ^ 2 = (s * t) ^ 2 * g) ∧
    ∃ i : Fˣ, orderOf i = 4 := by
  intro bar hform U
  have hU2 : (U 2).ncard = 96 := by
    rw [← Nat.card_coe_set_eq]
    exact card_unitary_two hF
  have hU3 : (U 3).ncard = 24192 := by
    rw [← Nat.card_coe_set_eq]
    exact card_unitary_three hF
  refine ⟨?_, ncard_normOne_one hF, ncard_normOne_two hF, ncard_normOne_three hF, hU2, hU3,
    card_statedSU hF, statedScalars_subgroupOf_statedSU_eq_bot hF,
    isPerfect_statedSU_three_three hF,
    classicalModel_statedSU hF, wreath_sylow_model hF, exists_units_orderOf_eq_four hF⟩
  rw [coe_statedSU hF]
  rfl

end CFSG.LinearGroups.UnitaryThreeOverNine
