module

public import CFSG.CharacterTheory.Wreathed.Involutions

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def quarterScale (l : ℕ) : ZMod 4 →+ ZMod (4 * l) :=
  ZMod.lift 4 ⟨zmultiplesHom _ (l : ZMod (4 * l)), by
    rw [zmultiplesHom_apply, zsmul_eq_mul]
    norm_num only [Int.cast_ofNat]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (ZMod.natCast_self (4 * l))⟩

@[simp] theorem quarterScale_natCast (l k : ℕ) :
    quarterScale l (k : ZMod 4) = (k * l : ℕ) := by
  change ZMod.lift 4 _ ((k : ℤ) : ZMod 4) = _
  rw [ZMod.lift_coe]
  simp [zmultiplesHom_apply, zsmul_eq_mul]

@[simp] theorem quarterScale_one (l : ℕ) : quarterScale l 1 = l := by
  simpa using quarterScale_natCast l 1

@[simp] theorem quarterScale_two (l : ℕ) : quarterScale l 2 = (2 * l : ℕ) :=
  quarterScale_natCast l 2

theorem quarterScale_injective (l : ℕ) (hl : 0 < l) :
    Function.Injective (quarterScale l) := by
  intro i j hij
  have hi : i.val < 4 := ZMod.val_lt i
  have hj : j.val < 4 := ZMod.val_lt j
  have hival : (quarterScale l i).val = i.val * l := by
    conv_lhs => rw [← ZMod.natCast_zmod_val i]
    rw [quarterScale_natCast, ZMod.val_natCast_of_lt (by nlinarith)]
  have hjval : (quarterScale l j).val = j.val * l := by
    conv_lhs => rw [← ZMod.natCast_zmod_val j]
    rw [quarterScale_natCast, ZMod.val_natCast_of_lt (by nlinarith)]
  have heq := congrArg ZMod.val hij
  rw [hival, hjval] at heq
  apply ZMod.val_injective 4
  nlinarith

theorem twice_quarter_add_self (l : ℕ) :
    (2 * l : ℕ) + (2 * l : ℕ) = (0 : ZMod (4 * l)) := by
  rw [← Nat.cast_add, show 2 * l + 2 * l = 4 * l by omega, ZMod.natCast_self]

@[expose] def quaternionEightEmbedding (l : ℕ) : QuaternionGroup 2 →* Wreath (4 * l) where
  toFun
    | .a i => element (4 * l) (quarterScale l i) (-quarterScale l i) 0
    | .xa i => element (4 * l) ((2 * l : ℕ) - quarterScale l i) (quarterScale l i) 1
  map_one' := by
    change element (4 * l) (quarterScale l 0) (-quarterScale l 0) 0 = 1
    simp
  map_mul' g k := by
    cases g with
    | a i =>
      cases k with
      | a j =>
        change element (4 * l) (quarterScale l (i + j)) (-quarterScale l (i + j)) 0 = _
        rw [map_add, element_base_mul]
        congr 1
        abel
      | xa j =>
        change element (4 * l) ((2 * l : ℕ) - quarterScale l (j - i))
          (quarterScale l (j - i)) 1 = _
        rw [map_sub, element_base_mul]
        congr 1 <;> abel
    | xa i =>
      cases k with
      | a j =>
        change element (4 * l) ((2 * l : ℕ) - quarterScale l (i + j))
          (quarterScale l (i + j)) 1 = _
        rw [map_add, element_swap_mul, add_zero]
        congr 1
        abel
      | xa j =>
        change element (4 * l) (quarterScale l (2 + j - i))
          (-quarterScale l (2 + j - i)) 0 = _
        rw [map_sub, map_add, quarterScale_two, element_swap_mul,
          show (1 + 1 : ZMod 2) = 0 by decide, element_eq_iff]
        refine ⟨?_, ?_, rfl⟩
        · abel
        · linear_combination -(twice_quarter_add_self l)

theorem quaternionEightEmbedding_injective (l : ℕ) (hl : 0 < l) :
    Function.Injective (quaternionEightEmbedding l) := by
  intro g k heq
  cases g with
  | a i =>
    cases k with
    | a j =>
      change element (4 * l) (quarterScale l i) (-quarterScale l i) 0 =
        element (4 * l) (quarterScale l j) (-quarterScale l j) 0 at heq
      have hij := ((element_eq_iff _ _ _ _ _ _ _).mp heq).1
      rw [quarterScale_injective l hl hij]
    | xa j =>
      change element (4 * l) (quarterScale l i) (-quarterScale l i) 0 =
        element (4 * l) ((2 * l : ℕ) - quarterScale l j) (quarterScale l j) 1 at heq
      exact False.elim (zero_ne_one ((element_eq_iff _ _ _ _ _ _ _).mp heq).2.2)
  | xa i =>
    cases k with
    | a j =>
      change element (4 * l) ((2 * l : ℕ) - quarterScale l i) (quarterScale l i) 1 =
        element (4 * l) (quarterScale l j) (-quarterScale l j) 0 at heq
      exact False.elim (one_ne_zero ((element_eq_iff _ _ _ _ _ _ _).mp heq).2.2)
    | xa j =>
      change element (4 * l) ((2 * l : ℕ) - quarterScale l i) (quarterScale l i) 1 =
        element (4 * l) ((2 * l : ℕ) - quarterScale l j) (quarterScale l j) 1 at heq
      have hij := ((element_eq_iff _ _ _ _ _ _ _).mp heq).2.1
      rw [quarterScale_injective l hl hij]

@[expose] def quaternionEightSubgroup (l : ℕ) : Subgroup (Wreath (4 * l)) :=
  (quaternionEightEmbedding l).range

@[expose] def quaternionEightRangeEquiv (l : ℕ) (hl : 0 < l) :
    QuaternionGroup 2 ≃* quaternionEightSubgroup l :=
  MonoidHom.ofInjective (quaternionEightEmbedding_injective l hl)

theorem card_quaternionEightSubgroup (l : ℕ) (hl : 0 < l) :
    Nat.card (quaternionEightSubgroup l) = 8 := by
  rw [← Nat.card_congr (quaternionEightRangeEquiv l hl).toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem quaternionEight_range_eq_generated (l : ℕ) :
    quaternionEightSubgroup l = Subgroup.closure
      {element (4 * l) l (-l) 0, element (4 * l) (2 * l : ℕ) 0 1} := by
  apply le_antisymm
  · rintro g ⟨a, rfl⟩
    let H := Subgroup.closure
      {element (4 * l) l (-l) 0, element (4 * l) (2 * l : ℕ) 0 1}
    have hr : element (4 * l) l (-l) 0 ∈ H := Subgroup.subset_closure (by simp)
    have hd : element (4 * l) (2 * l : ℕ) 0 1 ∈ H := Subgroup.subset_closure (by simp)
    have hrot (i : ZMod 4) : (quaternionEightEmbedding l) (.a i) ∈ H := by
      have hp := H.pow_mem hr i.val
      have hgen : (quaternionEightEmbedding l) (QuaternionGroup.a 1) =
          element (4 * l) l (-l) 0 := by
        change element (4 * l) (quarterScale l 1) (-quarterScale l 1) 0 = _
        rw [quarterScale_one]
      rw [← hgen, ← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val] at hp
      exact hp
    cases a with
    | a i => exact hrot i
    | xa i =>
      have hp := H.mul_mem hd (hrot i)
      change element (4 * l) (2 * l : ℕ) 0 1 *
        element (4 * l) (quarterScale l i) (-quarterScale l i) 0 ∈ H at hp
      rw [element_swap_mul, add_zero] at hp
      change element (4 * l) ((2 * l : ℕ) - quarterScale l i) (quarterScale l i) 1 ∈ H
      simpa only [sub_eq_add_neg, zero_add] using hp
  · rw [Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hg1 | hg2
    · rw [hg1]
      refine ⟨QuaternionGroup.a 1, ?_⟩
      change element (4 * l) (quarterScale l 1) (-quarterScale l 1) 0 = _
      rw [quarterScale_one]
    · rw [Set.mem_singleton_iff.mp hg2]
      refine ⟨QuaternionGroup.xa 0, ?_⟩
      change element (4 * l) ((2 * l : ℕ) - quarterScale l 0) (quarterScale l 0) 1 = _
      simp

theorem quaternionEight_range_eq_original_generators (l : ℕ) :
    quaternionEightSubgroup l = Subgroup.closure
      {(element (4 * l) 1 (-1) 0) ^ l, element (4 * l) (2 * l : ℕ) 0 1} := by
  rw [element_base_pow]
  simpa only [nsmul_eq_mul, mul_one, mul_neg] using quaternionEight_range_eq_generated l

theorem quaternionEight_mem_center_iff (l : ℕ) (hl : 0 < l) (g : QuaternionGroup 2) :
    (quaternionEightEmbedding l) g ∈ Subgroup.center (Wreath (4 * l)) ↔
      g = 1 ∨ g = QuaternionGroup.a 2 := by
  have hm : 1 < 4 * l := by omega
  cases g with
  | a i =>
    change element (4 * l) (quarterScale l i) (-quarterScale l i) 0 ∈
      Subgroup.center (Wreath (4 * l)) ↔ _
    rw [element_mem_center_iff _ hm]
    simp only [true_and, ← map_neg, (quarterScale_injective l hl).eq_iff,
      QuaternionGroup.one_def, QuaternionGroup.a.injEq]
    exact (show ∀ i : ZMod 4, i = -i ↔ i = 0 ∨ i = 2 by decide) i
  | xa i =>
    change element (4 * l) ((2 * l : ℕ) - quarterScale l i) (quarterScale l i) 1 ∈
      Subgroup.center (Wreath (4 * l)) ↔ _
    rw [element_mem_center_iff _ hm]
    simp [QuaternionGroup.one_def, -QuaternionGroup.a_zero]

theorem quaternionEight_center_intersection (l : ℕ) (hl : 0 < l) :
    Subgroup.center (Wreath (4 * l)) ⊓ quaternionEightSubgroup l =
      Subgroup.zpowers (element (4 * l) (2 * l : ℕ) (2 * l : ℕ) 0) := by
  let x := element (4 * l) (2 * l : ℕ) (2 * l : ℕ) 0
  have hx : (quaternionEightEmbedding l) (QuaternionGroup.a 2) = x := by
    change element (4 * l) (quarterScale l 2) (-quarterScale l 2) 0 = x
    rw [quarterScale_two]
    have hneg : -((2 * l : ℕ) : ZMod (4 * l)) = (2 * l : ℕ) := by
      linear_combination -(twice_quarter_add_self l)
    rw [hneg]
  apply le_antisymm
  · rintro g ⟨hz, ⟨q, hq⟩⟩
    rw [← hq] at hz ⊢
    rcases (quaternionEight_mem_center_iff l hl q).mp hz with h | h
    · rw [h, map_one]
      exact Subgroup.one_mem _
    · rw [h, hx]
      exact Subgroup.mem_zpowers x
  · rw [Subgroup.zpowers_le]
    refine ⟨?_, ?_⟩
    · change x ∈ Subgroup.center (Wreath (4 * l))
      rw [← hx]
      exact (quaternionEight_mem_center_iff l hl (QuaternionGroup.a 2)).mpr (Or.inr rfl)
    · exact ⟨QuaternionGroup.a 2, hx⟩

end CFSG.Wreathed
