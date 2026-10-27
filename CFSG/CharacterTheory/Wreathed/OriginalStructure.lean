module

public import CFSG.CharacterTheory.Wreathed.OriginalCoordinates
public import CFSG.CharacterTheory.Wreathed.AutomorphismTwoGroup
public import CFSG.CharacterTheory.Wreathed.VNormalizer
public import CFSG.CharacterTheory.Wreathed.VQuotientCycle

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

namespace Original

theorem element_eq_powers (m : ℕ) (hm : 0 < m)
    (i j : ZMod m) (e : ZMod 2) :
    element m i j e = s m ^ i.val * t m ^ j.val * z m ^ e.val := by
  let : NeZero m := ⟨by omega⟩
  have hs : s m ^ i.val = element m i 0 0 := by
    simp [s, element_base_pow, nsmul_eq_mul]
  have ht : t m ^ j.val = element m 0 j 0 := by
    simp [t, element_base_pow, nsmul_eq_mul]
  rw [hs, ht, element_base_mul, add_zero, zero_add]
  rcases swap_exponent_cases e with rfl | rfl
  · simp [z]
  · rw [show (1 : ZMod 2).val = 1 by decide, pow_one, z, element_base_mul]
    simp

theorem unique_coordinates (m : ℕ) (hm : 0 < m) (g : Wreath m) :
    ∃! c : ZMod m × ZMod m × ZMod 2,
      g = s m ^ c.1.val * t m ^ c.2.1.val * z m ^ c.2.2.val := by
  refine ⟨coordinateEquiv m g, ?_, ?_⟩
  · change g = s m ^ (coordinateEquiv m g).1.val *
      t m ^ (coordinateEquiv m g).2.1.val * z m ^ (coordinateEquiv m g).2.2.val
    rw [← element_eq_powers m hm]
    exact ((coordinateEquiv m).symm_apply_apply g).symm
  · intro c hc
    rw [← element_eq_powers m hm] at hc
    exact ((coordinateEquiv m).symm.injective
      (hc.symm.trans ((coordinateEquiv m).symm_apply_apply g).symm))

theorem x_conjugacy (m : ℕ) (g : Wreath m) :
    IsConj (x m) g ↔ g = x m := by
  simp only [x_eq, base_conjugacy_iff, or_self]

theorem x2_conjugacy (m : ℕ) (g : Wreath m) :
    IsConj (x2 m) g ↔ g = x2 m ∨ g = t m ^ (m / 2) := by
  simp only [x2_eq, t, element_base_pow, nsmul_eq_mul, mul_zero, mul_one,
    base_conjugacy_iff]

theorem z_conjugacy (m : ℕ) (hm : 0 < m) (g : Wreath m) :
    IsConj (z m) g ↔ ∃ i : ZMod m, g = r m ^ i.val * z m := by
  let : NeZero m := ⟨by omega⟩
  have hpow (i : ZMod m) : r m ^ i.val * z m = element m i (-i) 1 := by
    rw [r_eq, element_base_pow, z, element_base_mul]
    simp [nsmul_eq_mul]
  simp_rw [hpow]
  exact swap_conjugacy_iff m g

theorem three_involution_classes_atQuarter (l : ℕ) (hl : 0 < l)
    (g : Wreath (4 * l)) (hg : orderOf g = 2) :
    IsConj (x (4 * l)) g ∨ IsConj (x2 (4 * l)) g ∨ IsConj (z (4 * l)) g := by
  have hbase (i j : ZMod (4 * l))
      (h : orderOf (element (4 * l) i j 0) = 2) :
      (i = (2 * l : ℕ) ∧ j = (2 * l : ℕ)) ∨
      (i = (2 * l : ℕ) ∧ j = 0) ∨ (i = 0 ∧ j = (2 * l : ℕ)) := by
    rw [orderOf_eq_prime_iff, element_base_pow, element_base_eq_one_iff,
      two_smul_eq_zero_half_quarter l hl, two_smul_eq_zero_half_quarter l hl,
      ne_eq, element_base_eq_one_iff] at h
    have hne := half_quarter_ne_zero l hl
    rcases h with ⟨⟨hi, hj⟩, hn⟩
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all
  obtain ⟨⟨i, j, e⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective g
  change orderOf (element (4 * l) i j e) = 2 at hg
  change IsConj _ (element (4 * l) i j e) ∨
    IsConj _ (element (4 * l) i j e) ∨ IsConj _ (element (4 * l) i j e)
  simp only [x_eq, x2_eq, z, show 4 * l / 2 = 2 * l by omega]
  rcases swap_exponent_cases e with rfl | rfl
  · rcases hbase i j hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (IsConj.refl _)
    · exact Or.inr (Or.inl (IsConj.refl _))
    · exact Or.inr (Or.inl ((base_conjugacy_iff _ _ _ _).mpr (Or.inr rfl)))
  · have hj : j = -i := by
      have hsum := (element_swap_involution_iff _ i j).mp hg
      linear_combination hsum
    subst j
    exact Or.inr (Or.inr (outside_involution_conjugate _ i))

theorem three_representatives_distinct_atQuarter (l : ℕ) (hl : 0 < l) :
    ¬ IsConj (x (4 * l)) (x2 (4 * l)) ∧
    ¬ IsConj (x (4 * l)) (z (4 * l)) ∧
    ¬ IsConj (x2 (4 * l)) (z (4 * l)) := by
  have hn := half_quarter_ne_zero l hl
  simp only [x_eq, x2_eq, z, show 4 * l / 2 = 2 * l by omega,
    base_conjugacy_iff, element_eq_iff, eq_self, one_ne_zero,
    Ne.symm hn, and_false, false_or, not_false_eq_true, and_true]

end Original

structure OriginalStructure (m : ℕ) : Prop where
  coordinates : ∀ g : Wreath m, ∃! c : ZMod m × ZMod m × ZMod 2,
    g = Original.s m ^ c.1.val * Original.t m ^ c.2.1.val * Original.z m ^ c.2.2.val
  generator_orders : orderOf (Original.s m) = m ∧ orderOf (Original.t m) = m ∧
    orderOf (Original.a m) = m ∧ orderOf (Original.r m) = m ∧ orderOf (Original.z m) = 2
  swap : Original.z m * Original.s m * (Original.z m)⁻¹ = Original.t m
  card : Nat.card (Wreath m) = 2 * m ^ 2
  center : Subgroup.center (Wreath m) = Original.Z m
  derived : commutator (Wreath m) = Subgroup.zpowers (Original.r m)
  dihedral : Nonempty (Wreath m ⧸ Subgroup.center (Wreath m) ≃* DihedralGroup m)
  dihedral_card : Nat.card (Wreath m ⧸ Subgroup.center (Wreath m)) = 2 * m
  involution_orders : orderOf (Original.x m) = 2 ∧ orderOf (Original.x2 m) = 2 ∧
    orderOf (Original.z m) = 2 ∧ orderOf (Original.d m) = 4
  involution_classes : ∀ g : Wreath m, orderOf g = 2 →
    IsConj (Original.x m) g ∨ IsConj (Original.x2 m) g ∨ IsConj (Original.z m) g
  distinct_classes : ¬ IsConj (Original.x m) (Original.x2 m) ∧
    ¬ IsConj (Original.x m) (Original.z m) ∧ ¬ IsConj (Original.x2 m) (Original.z m)
  x_class : ∀ g : Wreath m, IsConj (Original.x m) g ↔ g = Original.x m
  x2_class : ∀ g : Wreath m, IsConj (Original.x2 m) g ↔
    g = Original.x2 m ∨ g = Original.t m ^ (m / 2)
  z_class : ∀ g : Wreath m, IsConj (Original.z m) g ↔
    ∃ i : ZMod m, g = Original.r m ^ i.val * Original.z m
  base_abelian : IsMulCommutative (Original.U m)
  base_index : (Original.U m).index = 2
  base_unique : ∀ P : Subgroup (Wreath m), IsMulCommutative P → P.index = 2 → P = Original.U m
  base_characteristic : (Original.U m).Characteristic
  automorphisms : IsPGroup 2 (MulAut (Wreath m))
  nonabelian_centralizers : ∀ P : Subgroup (Wreath m), (∃ u v : P, u * v ≠ v * u) →
    Subgroup.centralizer (P : Set (Wreath m)) = Original.Z m ∧
      (Subgroup.center P).map P.subtype = P ⊓ Original.Z m
  quaternion : Nonempty (QuaternionGroup (m / 2) ≃* Original.Y m)
  quaternion_card : Nat.card (Original.Y m) = 2 * m
  quaternion_quotient : ∃ h : (Original.Y m).Normal,
    letI := h
    Nonempty (Wreath m ⧸ Original.Y m ≃* Multiplicative (ZMod m)) ∧
      Nat.card (Wreath m ⧸ Original.Y m) = m ∧ IsCyclic (Wreath m ⧸ Original.Y m)
  normal_closure : Subgroup.normalClosure {Original.d m} = Original.Y m
  quaternion_eight : Nonempty (QuaternionGroup 2 ≃* Original.Q m)
  quaternion_eight_card : Nat.card (Original.Q m) = 8
  central_product : Original.V m = Original.Z m ⊔ Original.Q m
  intersection : Original.Z m ⊓ Original.Q m = Subgroup.zpowers (Original.x m)
  central_product_card : Nat.card (Original.V m) = 4 * m
  central_product_centralizer : Subgroup.centralizer (Original.V m : Set (Wreath m)) = Original.Z m
  central_product_center : (Subgroup.center (Original.V m)).map (Original.V m).subtype = Original.Z m
  normalizer_card : Nat.card (Subgroup.normalizer (Original.V m : Set (Wreath m))) = 8 * m
  normalizer_index : (Original.V m).relIndex (Subgroup.normalizer (Original.V m : Set (Wreath m))) = 2
  quaternion_characteristic : ((Original.Q m).subgroupOf (Original.V m)).Characteristic
  order_four : ∀ g : Wreath m, g ∈ Original.V m → g ∉ Original.Z m →
    (orderOf g = 4 ↔ g ∈ Original.Q m)
  six : Nat.card {g : Original.V m | g.val ∉ Original.Z m ∧ orderOf g = 4} = 6
  cycle : ∃ α : MulAut (Original.V m), orderOf α = 3 ∧
    (∀ g : Original.V m, g.val ∈ Original.Z m → α g = g) ∧
    ∃ β : MulAut (Original.V m ⧸ Subgroup.center (Original.V m)),
      (∀ g : Original.V m,
        β ((QuotientGroup.mk' (Subgroup.center (Original.V m))) g) =
          (QuotientGroup.mk' (Subgroup.center (Original.V m))) (α g)) ∧
      ∃ u v w : Original.V m ⧸ Subgroup.center (Original.V m),
        u ≠ 1 ∧ v ≠ 1 ∧ w ≠ 1 ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
          (∀ q : Original.V m ⧸ Subgroup.center (Original.V m),
            q = 1 ∨ q = u ∨ q = v ∨ q = w) ∧ β u = v ∧ β v = w ∧ β w = u

theorem original_structure_atQuarter (l : ℕ) (hl : 0 < l)
    (haut : IsPGroup 2 (MulAut (Wreath (4 * l)))) : OriginalStructure (4 * l) := by
  have hm : 2 < 4 * l := by omega
  have hz : Original.Z (4 * l) = Subgroup.center (Wreath (4 * l)) := Original.Z_eq _ (by omega)
  have hy := Original.Y_atQuarter l
  have hq := Original.Q_atQuarter l
  have hv := Original.V_atQuarter l
  refine {
    coordinates := Original.unique_coordinates _ (by omega)
    generator_orders := ⟨Original.orderOf_s _, Original.orderOf_t _, Original.orderOf_a _,
      Original.orderOf_r _, Original.orderOf_z _⟩
    swap := Original.z_conjugates_s _
    card := card_wreath _
    center := hz.symm
    derived := Original.derived_eq _
    dihedral := ⟨centerQuotientEquivDihedral _ (by omega)⟩
    dihedral_card := card_center_quotient _ (by omega)
    involution_orders := ⟨Original.orderOf_x_atQuarter l hl, Original.orderOf_x2_atQuarter l hl,
      Original.orderOf_z _, Original.orderOf_d_atQuarter l hl⟩
    involution_classes := Original.three_involution_classes_atQuarter l hl
    distinct_classes := Original.three_representatives_distinct_atQuarter l hl
    x_class := Original.x_conjugacy _
    x2_class := Original.x2_conjugacy _
    z_class := Original.z_conjugacy _ (by omega)
    base_abelian := by rw [Original.U_eq]; exact base_is_abelian _
    base_index := by rw [Original.U_eq]; exact base_index_two _ (by omega)
    base_unique := by rw [Original.U_eq]; exact unique_abelian_index_two _ hm
    base_characteristic := by rw [Original.U_eq]; exact base_characteristic _ hm
    automorphisms := haut
    nonabelian_centralizers := ?_
    quaternion := ?_
    quaternion_card := by rw [hy]; exact card_quaternionAtQuarter l hl
    quaternion_quotient := ?_
    normal_closure := ?_
    quaternion_eight := by rw [hq]; exact ⟨quaternionEightRangeEquiv l hl⟩
    quaternion_eight_card := by rw [hq]; exact card_quaternionEightSubgroup l hl
    central_product := by rw [hv, hz, hq]; exact v_eq_center_sup_quaternionEight l hl
    intersection := ?_
    central_product_card := by rw [hv]; exact card_vSubgroup l hl
    central_product_centralizer := by rw [hv, hz]; exact v_centralizer_eq_center l hl
    central_product_center := by rw [hv, hz]; exact v_center_map l hl
    normalizer_card := by rw [hv]; exact card_v_normalizer l hl
    normalizer_index := by rw [hv]; exact v_normalizer_index_two l hl
    quaternion_characteristic := by rw [hq, hv]; exact quaternionInV_characteristic l hl
    order_four := by rw [hv, hz, hq]; exact v_noncentral_order_four_iff l hl
    six := ?_
    cycle := ?_ }
  · intro P hP
    rw [hz]
    exact ⟨nonabelian_subgroup_centralizer_eq_center _ (by omega) P hP,
      nonabelian_subgroup_center _ (by omega) P hP⟩
  · rw [hy, show 4 * l / 2 = 2 * l by omega]
    exact ⟨quaternionAtQuarterEquiv l⟩
  · have hnormal : (Original.Y (4 * l)).Normal := by rw [hy]; infer_instance
    refine ⟨hnormal, ?_⟩
    have he : Wreath (4 * l) ⧸ Original.Y (4 * l) ≃* Multiplicative (ZMod (4 * l)) :=
      (QuotientGroup.quotientMulEquivOfEq hy).trans (quaternionAtQuarterQuotientEquiv l)
    refine ⟨⟨he⟩, ?_, he.isCyclic.mpr inferInstance⟩
    rw [Nat.card_congr he.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  · rw [hy, Original.d_eq, show 4 * l / 2 = 2 * l by omega]
    exact normalClosure_d_atQuarter l
  · rw [hz, hq, Original.x_eq, show 4 * l / 2 = 2 * l by omega]
    exact quaternionEight_center_intersection l hl
  · rw [hv, hz]
    have hset : {g : vSubgroup l | g.val ∉ Subgroup.center (Wreath (4 * l)) ∧ orderOf g = 4} =
        {g : vSubgroup l | g ∉ Subgroup.center (vSubgroup l) ∧ orderOf g = 4} := by
      ext g
      simp only [Set.mem_ofPred_eq, v_mem_center_iff l hl]
    rw [hset]
    exact card_v_noncentral_order_four l hl
  · rw [hv, hz]
    refine ⟨vCycle l hl, vCycle_order l hl, ?_, vCycleQuotient l hl, ?_,
      vQuotientQuaternionProjection l (QuaternionGroup.a 1),
      vQuotientQuaternionProjection l (QuaternionGroup.xa 0),
      vQuotientQuaternionProjection l (QuaternionGroup.xa 3), ?_⟩
    · intro g hg
      exact vCycle_fixes_center l hl g ((v_mem_center_iff l hl g).mpr hg)
    · intro g
      change QuotientGroup.congr _ _ _ _
        (g : vSubgroup l ⧸ Subgroup.center (vSubgroup l)) = _
      rw [QuotientGroup.congr_mk]
      rfl
    · rcases v_quotient_representatives_distinct l hl with ⟨hu, hv, hw, huv, huw, hvw⟩
      rcases vCycleQuotient_cycles_three l hl with ⟨hc0, hc1, hc2⟩
      exact ⟨hu, hv, hw, huv, huw, hvw, v_quotient_three_nonzero l hl, hc0, hc1, hc2⟩

theorem wreath_center_involution_and_quaternion_coordinates (n : ℕ) (hn : 2 ≤ n) :
    OriginalStructure (2 ^ n) := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    have hheight : n = (n - 2) + 2 := by omega
    calc
      2 ^ n = 2 ^ ((n - 2) + 2) := congrArg (fun j : ℕ => 2 ^ j) hheight
      _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; norm_num; ring
  have haut := wreath_automorphism_isPGroup n hn
  rw [hm] at haut ⊢
  exact original_structure_atQuarter _ (pow_pos (by decide) _) haut

end CFSG.Wreathed
