module

public import CFSG.CharacterTheory.Wreathed.QuaternionEight
public import CFSG.CharacterTheory.Wreathed.NonabelianCentralizer

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem half_quarter_ne_zero (l : ℕ) (hl : 0 < l) :
    ((2 * l : ℕ) : ZMod (4 * l)) ≠ 0 := by
  intro heq
  have hv := congrArg ZMod.val heq
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
  omega

theorem half_difference_add (l : ℕ) (a b : ZMod (4 * l))
    (ha : a = 0 ∨ a = (2 * l : ℕ)) (hb : b = 0 ∨ b = (2 * l : ℕ)) :
    a + b = 0 ∨ a + b = (2 * l : ℕ) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp
  · simp
  · simp
  · exact Or.inl (twice_quarter_add_self l)

theorem half_difference_neg (l : ℕ) (a : ZMod (4 * l))
    (ha : a = 0 ∨ a = (2 * l : ℕ)) :
    -a = 0 ∨ -a = (2 * l : ℕ) := by
  rcases ha with rfl | rfl
  · simp
  · right
    linear_combination -(twice_quarter_add_self l)

@[expose] def vSubgroup (l : ℕ) : Subgroup (Wreath (4 * l)) where
  carrier := {g | (coordinateEquiv (4 * l) g).1 - (coordinateEquiv (4 * l) g).2.1 = 0 ∨
    (coordinateEquiv (4 * l) g).1 - (coordinateEquiv (4 * l) g).2.1 = (2 * l : ℕ)}
  one_mem' := by
    change (0 : ZMod (4 * l)) - 0 = 0 ∨ (0 : ZMod (4 * l)) - 0 = (2 * l : ℕ)
    simp
  mul_mem' {g k} hg hk := by
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective g
    obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective k
    change a - b = 0 ∨ a - b = (2 * l : ℕ) at hg
    change c - d = 0 ∨ c - d = (2 * l : ℕ) at hk
    change (coordinateEquiv (4 * l) (element (4 * l) a b e * element (4 * l) c d f)).1 -
      (coordinateEquiv (4 * l) (element (4 * l) a b e * element (4 * l) c d f)).2.1 = 0 ∨
      (coordinateEquiv (4 * l) (element (4 * l) a b e * element (4 * l) c d f)).1 -
      (coordinateEquiv (4 * l) (element (4 * l) a b e * element (4 * l) c d f)).2.1 = (2 * l : ℕ)
    rcases swap_exponent_cases e with rfl | rfl
    · rw [element_base_mul]
      change (a + c) - (b + d) = 0 ∨ (a + c) - (b + d) = (2 * l : ℕ)
      have heq : (a + c) - (b + d) = (a - b) + (c - d) := by abel
      rw [heq]
      exact half_difference_add l _ _ hg hk
    · rw [element_swap_mul]
      change (a + d) - (b + c) = 0 ∨ (a + d) - (b + c) = (2 * l : ℕ)
      have heq : (a + d) - (b + c) = (a - b) + -(c - d) := by abel
      rw [heq]
      exact half_difference_add l _ _ hg (half_difference_neg l _ hk)
  inv_mem' {g} hg := by
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective g
    change a - b = 0 ∨ a - b = (2 * l : ℕ) at hg
    change (coordinateEquiv (4 * l) ((element (4 * l) a b e)⁻¹)).1 -
      (coordinateEquiv (4 * l) ((element (4 * l) a b e)⁻¹)).2.1 = 0 ∨
      (coordinateEquiv (4 * l) ((element (4 * l) a b e)⁻¹)).1 -
      (coordinateEquiv (4 * l) ((element (4 * l) a b e)⁻¹)).2.1 = (2 * l : ℕ)
    rcases swap_exponent_cases e with rfl | rfl
    · rw [element_base_inv]
      change -a - -b = 0 ∨ -a - -b = (2 * l : ℕ)
      have heq : -a - -b = -(a - b) := by abel
      rw [heq]
      exact half_difference_neg l _ hg
    · rw [element_swap_inv]
      change -b - -a = 0 ∨ -b - -a = (2 * l : ℕ)
      have heq : -b - -a = a - b := by abel
      rw [heq]
      exact hg

@[simp] theorem element_mem_v (l : ℕ) (a b : ZMod (4 * l)) (e : ZMod 2) :
    element (4 * l) a b e ∈ vSubgroup l ↔ a - b = 0 ∨ a - b = (2 * l : ℕ) :=
  Iff.rfl

@[expose] def vCoordinateMap (l : ℕ) (c : ZMod (4 * l) × Bool × ZMod 2) : vSubgroup l :=
  ⟨element (4 * l) (c.1 + if c.2.1 then ((2 * l : ℕ) : ZMod (4 * l)) else 0) c.1 c.2.2, by
    rw [element_mem_v]
    cases c.2.1 <;> simp⟩

theorem vCoordinateMap_injective (l : ℕ) (hl : 0 < l) :
    Function.Injective (vCoordinateMap l) := by
  rintro ⟨a, b, e⟩ ⟨c, d, f⟩ heq
  have hcoord := (element_eq_iff _ _ _ _ _ _ _).mp (congrArg Subtype.val heq)
  have hac : a = c := hcoord.2.1
  have hef : e = f := hcoord.2.2
  subst c
  subst f
  have hbd : b = d := by
    cases b <;> cases d
    · rfl
    · have hbad : ((2 * l : ℕ) : ZMod (4 * l)) = 0 := by
        simpa using (add_left_cancel hcoord.1).symm
      exact False.elim (half_quarter_ne_zero l hl hbad)
    · have hbad : ((2 * l : ℕ) : ZMod (4 * l)) = 0 := by
        simpa using add_left_cancel hcoord.1
      exact False.elim (half_quarter_ne_zero l hl hbad)
    · rfl
  rw [hbd]

theorem vCoordinateMap_surjective (l : ℕ) : Function.Surjective (vCoordinateMap l) := by
  intro g
  obtain ⟨⟨a, b, e⟩, heq⟩ := (coordinateEquiv (4 * l)).symm.surjective g.val
  change element (4 * l) a b e = g.val at heq
  have hg : element (4 * l) a b e ∈ vSubgroup l := heq ▸ g.property
  rcases (element_mem_v _ _ _ _).mp hg with h | h
  · refine ⟨(b, false, e), ?_⟩
    apply Subtype.ext
    change element (4 * l) (b + 0) b e = g.val
    rw [add_zero, ← heq, sub_eq_zero.mp h]
  · refine ⟨(b, true, e), ?_⟩
    apply Subtype.ext
    change element (4 * l) (b + (2 * l : ℕ)) b e = g.val
    rw [← heq]
    congr 1
    linear_combination -h

@[expose] def vCoordinateEquiv (l : ℕ) (hl : 0 < l) :
    ZMod (4 * l) × Bool × ZMod 2 ≃ vSubgroup l :=
  Equiv.ofBijective (vCoordinateMap l)
    ⟨vCoordinateMap_injective l hl, vCoordinateMap_surjective l⟩

theorem card_vSubgroup (l : ℕ) (hl : 0 < l) : Nat.card (vSubgroup l) = 4 * (4 * l) := by
  rw [← Nat.card_congr (vCoordinateEquiv l hl), Nat.card_prod, Nat.card_prod,
    Nat.card_zmod, Nat.card_zmod, Nat.card_eq_fintype_card (α := Bool)]
  norm_num
  ring

theorem v_eq_original_generators (l : ℕ) :
    vSubgroup l = Subgroup.closure
      {element (4 * l) 1 1 0, element (4 * l) (2 * l : ℕ) 0 0, element (4 * l) 0 0 1} := by
  let H := Subgroup.closure
    {element (4 * l) 1 1 0, element (4 * l) (2 * l : ℕ) 0 0, element (4 * l) 0 0 1}
  have ha : element (4 * l) 1 1 0 ∈ H := Subgroup.subset_closure (by simp)
  have hx2 : element (4 * l) (2 * l : ℕ) 0 0 ∈ H := Subgroup.subset_closure (by simp)
  have hz : element (4 * l) 0 0 1 ∈ H := Subgroup.subset_closure (by simp)
  have hdiag (a : ZMod (4 * l)) : element (4 * l) a a 0 ∈ H := by
    have himg : element (4 * l) a a 0 ∈ (diagonalHom (4 * l)).range :=
      ⟨Multiplicative.ofAdd a, rfl⟩
    rw [diagonal_range_eq_zpowers] at himg
    exact Subgroup.zpowers_le_of_mem ha himg
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective g
    change element (4 * l) a b e ∈ vSubgroup l at hg
    change element (4 * l) a b e ∈ H
    have hbase : element (4 * l) a b 0 ∈ H := by
      rcases (element_mem_v _ _ _ _).mp hg with h | h
      · rw [sub_eq_zero.mp h]
        exact hdiag b
      · have hp := H.mul_mem (hdiag b) hx2
        rw [element_base_mul] at hp
        have hab : b + (2 * l : ℕ) = a := by linear_combination -h
        simpa only [hab, add_zero] using hp
    rcases swap_exponent_cases e with rfl | rfl
    · exact hbase
    · have hp := H.mul_mem hbase hz
      simpa only [element_base_mul, add_zero] using hp
  · rw [Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hg | hg
    · rw [hg]
      simp
    · rcases Set.mem_insert_iff.mp hg with hg | hg
      · rw [hg]
        simp
      · rw [Set.mem_singleton_iff.mp hg]
        simp

theorem center_le_v (l : ℕ) (hl : 0 < l) :
    Subgroup.center (Wreath (4 * l)) ≤ vSubgroup l := by
  intro g hg
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective g
  change element (4 * l) a b e ∈ Subgroup.center (Wreath (4 * l)) at hg
  rcases (element_mem_center_iff _ (by omega) a b e).mp hg with ⟨rfl, rfl⟩
  change element (4 * l) a a 0 ∈ vSubgroup l
  simp

theorem quaternionEight_le_v (l : ℕ) : quaternionEightSubgroup l ≤ vSubgroup l := by
  rw [quaternionEight_range_eq_generated, Subgroup.closure_le]
  intro g hg
  rcases Set.mem_insert_iff.mp hg with hg | hg
  · rw [hg]
    change element (4 * l) l (-l) 0 ∈ vSubgroup l
    rw [element_mem_v]
    right
    push_cast
    ring
  · rw [Set.mem_singleton_iff.mp hg]
    change element (4 * l) (2 * l : ℕ) 0 1 ∈ vSubgroup l
    simp

theorem v_eq_center_sup_quaternionEight (l : ℕ) (hl : 0 < l) :
    vSubgroup l = Subgroup.center (Wreath (4 * l)) ⊔ quaternionEightSubgroup l := by
  let H := Subgroup.center (Wreath (4 * l)) ⊔ quaternionEightSubgroup l
  have hdiag (a : ZMod (4 * l)) : element (4 * l) a a 0 ∈ H :=
    Subgroup.mem_sup_left ((element_mem_center_iff _ (by omega) a a 0).mpr ⟨rfl, rfl⟩)
  have hr : element (4 * l) l (-l) 0 ∈ H := by
    apply Subgroup.mem_sup_right
    rw [quaternionEight_range_eq_generated]
    exact Subgroup.subset_closure (by simp)
  have hd : element (4 * l) (2 * l : ℕ) 0 1 ∈ H := by
    apply Subgroup.mem_sup_right
    rw [quaternionEight_range_eq_generated]
    exact Subgroup.subset_closure (by simp)
  have hx2 : element (4 * l) (2 * l : ℕ) 0 0 ∈ H := by
    have hp := H.mul_mem (hdiag l) hr
    rw [element_base_mul] at hp
    simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add, add_neg_cancel] using hp
  have hz : element (4 * l) 0 0 1 ∈ H := by
    have hp := H.mul_mem (H.inv_mem hx2) hd
    rw [element_base_inv, element_base_mul] at hp
    simpa only [neg_add_cancel, neg_zero, add_zero] using hp
  apply le_antisymm
  · rw [v_eq_original_generators, Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hg | hg
    · exact hg ▸ hdiag 1
    · rcases Set.mem_insert_iff.mp hg with hg | hg
      · exact hg ▸ hx2
      · exact Set.mem_singleton_iff.mp hg ▸ hz
  · exact sup_le (center_le_v l hl) (quaternionEight_le_v l)

@[expose] def centralProductProjection (l : ℕ) :
    Multiplicative (ZMod (4 * l)) × QuaternionGroup 2 →* Wreath (4 * l) :=
  (diagonalHom (4 * l)).noncommCoprod (quaternionEightEmbedding l) (by
    intro a q
    cases q with
    | a i =>
      change element (4 * l) (Multiplicative.toAdd a) (Multiplicative.toAdd a) 0 *
          element (4 * l) (quarterScale l i) (-quarterScale l i) 0 =
        element (4 * l) (quarterScale l i) (-quarterScale l i) 0 *
          element (4 * l) (Multiplicative.toAdd a) (Multiplicative.toAdd a) 0
      simp only [element_base_mul, add_comm]
    | xa i =>
      change element (4 * l) (Multiplicative.toAdd a) (Multiplicative.toAdd a) 0 *
          element (4 * l) ((2 * l : ℕ) - quarterScale l i) (quarterScale l i) 1 =
        element (4 * l) ((2 * l : ℕ) - quarterScale l i) (quarterScale l i) 1 *
          element (4 * l) (Multiplicative.toAdd a) (Multiplicative.toAdd a) 0
      simp only [element_base_mul, element_swap_mul, zero_add, add_comm])

theorem centralProductProjection_range (l : ℕ) (hl : 0 < l) :
    (centralProductProjection l).range = vSubgroup l := by
  rw [centralProductProjection, MonoidHom.noncommCoprod_range,
    ← center_eq_diagonal_range _ (by omega)]
  exact (v_eq_center_sup_quaternionEight l hl).symm

theorem v_is_nonabelian (l : ℕ) (hl : 0 < l) :
    ∃ x y : vSubgroup l, x * y ≠ y * x := by
  let x : vSubgroup l := ⟨element (4 * l) (2 * l : ℕ) 0 0, by simp⟩
  let y : vSubgroup l := ⟨element (4 * l) 0 0 1, by simp⟩
  refine ⟨x, y, ?_⟩
  intro h
  have heq := congrArg Subtype.val h
  have hc : Commute (element (4 * l) (2 * l : ℕ) 0 0) (element (4 * l) 0 0 1) := heq
  exact half_quarter_ne_zero l hl ((base_commutes_swap_iff _ _ _ _ _).mp hc)

theorem v_centralizer_eq_center (l : ℕ) (hl : 0 < l) :
    Subgroup.centralizer (vSubgroup l : Set (Wreath (4 * l))) =
      Subgroup.center (Wreath (4 * l)) :=
  nonabelian_subgroup_centralizer_eq_center _ (by omega) _ (v_is_nonabelian l hl)

end CFSG.Wreathed
