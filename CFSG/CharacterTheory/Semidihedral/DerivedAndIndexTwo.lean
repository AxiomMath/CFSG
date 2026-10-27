module

public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders

public section

namespace CFSG.Semidihedral

open CFSG.Open
open scoped commutatorElement

@[expose] def rotationReduction (n : ℕ) (hn : 3 ≤ n) :
    ZMod (modulus n) →+* ZMod 2 :=
  ZMod.castHom (show 2 ∣ modulus n from
    ⟨half n, modulus_eq_two_mul_half (by omega)⟩) (ZMod 2)

@[simp] theorem rotationReduction_apply (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) : rotationReduction n hn i = (i.val : ZMod 2) := by
  rw [rotationReduction, ZMod.castHom_apply, ZMod.cast_eq_val]

theorem rotationReduction_val (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) : (rotationReduction n hn i).val = i.val % 2 := by
  rw [rotationReduction_apply, ZMod.val_natCast]

@[simp] theorem rotationReduction_twist (n : ℕ) (hn : 3 ≤ n) :
    rotationReduction n hn (twist n) = 1 := by
  rw [twist, map_sub, map_natCast, map_one,
    (ZMod.natCast_eq_zero_iff_even).mpr (half_even hn)]
  decide

theorem element_coordinates (n : ℕ) (hn : 3 ≤ n) (g : SemidihedralGroup n) :
    element n hn (coordinateEquiv n hn g).1 (coordinateEquiv n hn g).2 = g :=
  (coordinateEquiv n hn).symm_apply_apply g

@[expose] def rotationParityHom (n : ℕ) (hn : 3 ≤ n) :
    SemidihedralGroup n →* Cyclic 2 where
  toFun g := Multiplicative.ofAdd
    (rotationReduction n hn (coordinateEquiv n hn g).1)
  map_one' := by
    rw [← element_zero_zero n hn, coordinateEquiv_element]
    simp
  map_mul' g h := by
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective g
    obtain ⟨⟨j, f⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective h
    change Multiplicative.ofAdd (rotationReduction n hn
      (coordinateEquiv n hn (element n hn i e * element n hn j f)).1) =
      Multiplicative.ofAdd (rotationReduction n hn
        (coordinateEquiv n hn (element n hn i e)).1) *
        Multiplicative.ofAdd (rotationReduction n hn
          (coordinateEquiv n hn (element n hn j f)).1)
    rw [coordinateEquiv_element, coordinateEquiv_element]
    rcases exponent_cases e with rfl | rfl
    · rw [element_rotation_mul, coordinateEquiv_element, map_add]
      rfl
    · rw [element_reflection_mul, coordinateEquiv_element, map_add, map_mul,
        rotationReduction_twist, one_mul]
      rfl

@[simp] theorem rotationParityHom_element (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    rotationParityHom n hn (element n hn i e) =
      Multiplicative.ofAdd (rotationReduction n hn i) := by
  change Multiplicative.ofAdd
    (rotationReduction n hn (coordinateEquiv n hn (element n hn i e)).1) = _
  rw [coordinateEquiv_element]

@[simp] theorem parityHom_element (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    parityHom n hn (element n hn i e) = Multiplicative.ofAdd e := by
  change (toModel n hn (element n hn i e)).right = Multiplicative.ofAdd e
  rw [toModel_element]
  rfl

@[expose] def mixedParityHom (n : ℕ) (hn : 3 ≤ n) :
    SemidihedralGroup n →* Cyclic 2 := rotationParityHom n hn * parityHom n hn

@[simp] theorem mixedParityHom_element (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    mixedParityHom n hn (element n hn i e) =
      Multiplicative.ofAdd (rotationReduction n hn i + e) := by
  simp only [mixedParityHom, MonoidHom.mul_apply, rotationParityHom_element,
    parityHom_element]
  rfl

theorem rotationReduction_eq_zero_iff (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) : rotationReduction n hn i = 0 ↔ i.val % 2 = 0 := by
  constructor
  · intro h
    simpa only [rotationReduction_val, ZMod.val_zero] using congrArg ZMod.val h
  · intro h
    apply ZMod.val_injective
    simpa only [rotationReduction_val, ZMod.val_zero] using h

theorem even_rotation_mem (n : ℕ) (hn : 3 ≤ n)
    (H : Subgroup (SemidihedralGroup n)) (hH : r n ^ 2 ∈ H)
    (i : ZMod (modulus n)) (hi : i.val % 2 = 0) : element n hn i 0 ∈ H := by
  have hv : i.val = 2 * (i.val / 2) := by omega
  rw [element_eq]
  simp only [ZMod.val_zero, pow_zero, mul_one]
  rw [hv, pow_mul]
  exact H.pow_mem hH _

theorem rotation_generator_eq_element (n : ℕ) (hn : 3 ≤ n) :
    r n = element n hn 1 0 := by
  simpa only [pow_one, Nat.cast_one] using r_pow_eq_element n hn 1

theorem r_sq_mem_dihedralSubgroup (n : ℕ) : r n ^ 2 ∈ dihedralSubgroup n :=
  Subgroup.subset_closure (by simp)

theorem s_mem_dihedralSubgroup (n : ℕ) : s n ∈ dihedralSubgroup n :=
  Subgroup.subset_closure (by simp)

theorem r_sq_mem_quaternionSubgroup (n : ℕ) : r n ^ 2 ∈ quaternionSubgroup n :=
  Subgroup.subset_closure (by simp)

theorem rs_mem_quaternionSubgroup (n : ℕ) : r n * s n ∈ quaternionSubgroup n :=
  Subgroup.subset_closure (by simp)

theorem dihedralSubgroup_le_rotationParity_ker (n : ℕ) (hn : 3 ≤ n) :
    dihedralSubgroup n ≤ (rotationParityHom n hn).ker := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · change rotationParityHom n hn (r n ^ 2) = 1
    rw [r_pow_eq_element n hn, rotationParityHom_element, map_natCast]
    rfl
  · change rotationParityHom n hn (s n) = 1
    rw [s_eq_element n hn, rotationParityHom_element, map_zero]
    rfl

theorem rotationParityHom_ker (n : ℕ) (hn : 3 ≤ n) :
    (rotationParityHom n hn).ker = dihedralSubgroup n := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective g
    change rotationParityHom n hn (element n hn i e) = 1 at hg
    rw [rotationParityHom_element] at hg
    have hi : i.val % 2 = 0 := (rotationReduction_eq_zero_iff n hn i).mp hg
    have hr := even_rotation_mem n hn (dihedralSubgroup n)
      (r_sq_mem_dihedralSubgroup n) i hi
    change element n hn i e ∈ dihedralSubgroup n
    rw [element_eq] at hr ⊢
    simp only [ZMod.val_zero, pow_zero, mul_one] at hr
    exact (dihedralSubgroup n).mul_mem hr
      ((dihedralSubgroup n).pow_mem (s_mem_dihedralSubgroup n) _)
  · exact dihedralSubgroup_le_rotationParity_ker n hn

theorem element_mem_dihedralSubgroup_iff (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    element n hn i e ∈ dihedralSubgroup n ↔ i.val % 2 = 0 := by
  rw [← rotationParityHom_ker n hn]
  change rotationParityHom n hn (element n hn i e) = 1 ↔ _
  rw [rotationParityHom_element]
  exact rotationReduction_eq_zero_iff n hn i

theorem quaternionSubgroup_le_mixedParity_ker (n : ℕ) (hn : 3 ≤ n) :
    quaternionSubgroup n ≤ (mixedParityHom n hn).ker := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · change mixedParityHom n hn (r n ^ 2) = 1
    rw [r_pow_eq_element n hn, mixedParityHom_element, map_natCast]
    rfl
  · change mixedParityHom n hn (r n * s n) = 1
    rw [rotation_generator_eq_element n hn, s_eq_element n hn,
      element_rotation_mul, add_zero, mixedParityHom_element, map_one]
    rfl

theorem odd_reflection_mem (n : ℕ) (hn : 3 ≤ n)
    (H : Subgroup (SemidihedralGroup n)) (hH : r n ^ 2 ∈ H)
    (hRS : r n * s n ∈ H) (i : ZMod (modulus n)) (hi : i.val % 2 = 1) :
    element n hn i 1 ∈ H := by
  have hv : i.val = 2 * (i.val / 2) + 1 := by omega
  have he : (r n ^ 2) ^ (i.val / 2) * (r n * s n) = element n hn i 1 := by
    rw [element_eq]
    simp only [ZMod.val_one, pow_one]
    rw [← pow_mul, ← mul_assoc, ← pow_succ, ← hv]
  rw [← he]
  exact H.mul_mem (H.pow_mem hH _) hRS

theorem mixedParity_zero_iff (a e : ZMod 2) : a + e = 0 ↔ a = e := by
  exact (show ∀ a e : ZMod 2, a + e = 0 ↔ a = e by decide) a e

theorem mixedParityHom_ker (n : ℕ) (hn : 3 ≤ n) :
    (mixedParityHom n hn).ker = quaternionSubgroup n := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective g
    change mixedParityHom n hn (element n hn i e) = 1 at hg
    rw [mixedParityHom_element] at hg
    have hp : rotationReduction n hn i = e := (mixedParity_zero_iff _ _).mp hg
    have hi : i.val % 2 = e.val := by
      simpa only [rotationReduction_val] using congrArg ZMod.val hp
    rcases exponent_cases e with rfl | rfl
    · exact even_rotation_mem n hn (quaternionSubgroup n)
        (r_sq_mem_quaternionSubgroup n) i (by simpa using hi)
    · exact odd_reflection_mem n hn (quaternionSubgroup n)
        (r_sq_mem_quaternionSubgroup n) (rs_mem_quaternionSubgroup n) i
        (by simpa only [ZMod.val_one] using hi)
  · exact quaternionSubgroup_le_mixedParity_ker n hn

theorem element_mem_quaternionSubgroup_iff (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    element n hn i e ∈ quaternionSubgroup n ↔ i.val % 2 = e.val := by
  rw [← mixedParityHom_ker n hn]
  change mixedParityHom n hn (element n hn i e) = 1 ↔ _
  rw [mixedParityHom_element]
  change rotationReduction n hn i + e = 0 ↔ _
  rw [mixedParity_zero_iff]
  constructor
  · intro h
    simpa only [rotationReduction_val] using congrArg ZMod.val h
  · intro h
    apply ZMod.val_injective
    simpa only [rotationReduction_val] using h

theorem rotationParityHom_surjective (n : ℕ) (hn : 3 ≤ n) :
    Function.Surjective (rotationParityHom n hn) := by
  intro e
  refine ⟨element n hn (e.toAdd.val : ZMod (modulus n)) 0, ?_⟩
  rw [rotationParityHom_element, map_natCast, ZMod.natCast_zmod_val]
  rfl

theorem mixedParityHom_surjective (n : ℕ) (hn : 3 ≤ n) :
    Function.Surjective (mixedParityHom n hn) := by
  intro e
  refine ⟨element n hn 0 e.toAdd, ?_⟩
  rw [mixedParityHom_element, map_zero, zero_add]
  rfl

theorem cyclicTwo_natCard : Nat.card (Cyclic 2) = 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem rotationSubgroup_index (n : ℕ) (hn : 3 ≤ n) :
    (rotationSubgroup n).index = 2 := rotation_index n hn

theorem dihedralSubgroup_index (n : ℕ) (hn : 3 ≤ n) :
    (dihedralSubgroup n).index = 2 := by
  rw [← rotationParityHom_ker n hn, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (rotationParityHom_surjective n hn)]
  rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (Cyclic 2)) ≃* Cyclic 2).toEquiv]
  exact cyclicTwo_natCard

theorem quaternionSubgroup_index (n : ℕ) (hn : 3 ≤ n) :
    (quaternionSubgroup n).index = 2 := by
  rw [← mixedParityHom_ker n hn, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (mixedParityHom_surjective n hn)]
  rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (Cyclic 2)) ≃* Cyclic 2).toEquiv]
  exact cyclicTwo_natCard

theorem rotationSubgroup_normal (n : ℕ) (hn : 3 ≤ n) :
    (rotationSubgroup n).Normal := Subgroup.normal_of_index_eq_two (rotationSubgroup_index n hn)

theorem dihedralSubgroup_normal (n : ℕ) (hn : 3 ≤ n) :
    (dihedralSubgroup n).Normal := Subgroup.normal_of_index_eq_two (dihedralSubgroup_index n hn)

theorem quaternionSubgroup_normal (n : ℕ) (hn : 3 ≤ n) :
    (quaternionSubgroup n).Normal :=
  Subgroup.normal_of_index_eq_two (quaternionSubgroup_index n hn)

theorem rotationSubgroup_cyclic (n : ℕ) : IsCyclic (rotationSubgroup n) := by
  change IsCyclic (Subgroup.zpowers (r n))
  infer_instance

theorem indexTwo_natCard (n : ℕ) (hn : 3 ≤ n)
    (H : Subgroup (SemidihedralGroup n)) (hH : H.index = 2) :
    Nat.card H = modulus n := by
  have hc := H.card_mul_index
  rw [hH, card n hn] at hc
  have he : n = n - 1 + 1 := by omega
  have ht : 2 ^ n = modulus n * 2 := by
    conv_lhs => rw [he, pow_succ]
    rfl
  rw [ht] at hc
  omega

theorem rotationSubgroup_natCard (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (rotationSubgroup n) = modulus n :=
  indexTwo_natCard n hn _ (rotationSubgroup_index n hn)

theorem dihedralSubgroup_natCard (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (dihedralSubgroup n) = modulus n :=
  indexTwo_natCard n hn _ (dihedralSubgroup_index n hn)

theorem quaternionSubgroup_natCard (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (quaternionSubgroup n) = modulus n :=
  indexTwo_natCard n hn _ (quaternionSubgroup_index n hn)

theorem element_mem_rotationSubgroup_iff (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    element n hn i e ∈ rotationSubgroup n ↔ e = 0 := by
  change element n hn i e ∈ Subgroup.zpowers (r n) ↔ _
  rw [← parityHom_ker n hn]
  change parityHom n hn (element n hn i e) = 1 ↔ _
  rw [parityHom_element]
  rfl

theorem r_not_mem_dihedralSubgroup (n : ℕ) (hn : 3 ≤ n) :
    r n ∉ dihedralSubgroup n := by
  rw [rotation_generator_eq_element n hn, element_mem_dihedralSubgroup_iff n hn]
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (modulus_two_le (by omega))]
  decide

theorem r_not_mem_quaternionSubgroup (n : ℕ) (hn : 3 ≤ n) :
    r n ∉ quaternionSubgroup n := by
  rw [rotation_generator_eq_element n hn, element_mem_quaternionSubgroup_iff n hn]
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (modulus_two_le (by omega)), ZMod.val_zero]
  decide

theorem s_not_mem_quaternionSubgroup (n : ℕ) (hn : 3 ≤ n) :
    s n ∉ quaternionSubgroup n := by
  rw [s_eq_element n hn, element_mem_quaternionSubgroup_iff n hn]
  rw [ZMod.val_zero, ZMod.val_one_eq_one_mod]
  decide

theorem rotationSubgroup_ne_dihedralSubgroup (n : ℕ) (hn : 3 ≤ n) :
    rotationSubgroup n ≠ dihedralSubgroup n := by
  intro h
  apply r_not_mem_dihedralSubgroup n hn
  rw [← h]
  exact Subgroup.mem_zpowers _

theorem rotationSubgroup_ne_quaternionSubgroup (n : ℕ) (hn : 3 ≤ n) :
    rotationSubgroup n ≠ quaternionSubgroup n := by
  intro h
  apply r_not_mem_quaternionSubgroup n hn
  rw [← h]
  exact Subgroup.mem_zpowers _

theorem dihedralSubgroup_ne_quaternionSubgroup (n : ℕ) (hn : 3 ≤ n) :
    dihedralSubgroup n ≠ quaternionSubgroup n := by
  intro h
  apply s_not_mem_quaternionSubgroup n hn
  rw [← h]
  exact s_mem_dihedralSubgroup n

theorem index_eq_two_iff (n : ℕ) (hn : 3 ≤ n)
    (H : Subgroup (SemidihedralGroup n)) :
    H.index = 2 ↔ H = rotationSubgroup n ∨ H = dihedralSubgroup n ∨
      H = quaternionSubgroup n := by
  constructor
  · intro hH
    let : Finite (SemidihedralGroup n) := presentation_finite n hn
    have hc := indexTwo_natCard n hn H hH
    have hr2 : r n ^ 2 ∈ H := Subgroup.sq_mem_of_index_two hH (r n)
    by_cases hr : r n ∈ H
    · left
      apply Eq.symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hr)
      change Nat.card H ≤ Nat.card (rotationSubgroup n)
      rw [hc, rotationSubgroup_natCard n hn]
    · by_cases hs : s n ∈ H
      · right
        left
        apply Eq.symm
        apply Subgroup.eq_of_le_of_card_ge
          ((Subgroup.closure_le H).mpr (by
            intro g hg
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
            rcases hg with rfl | rfl
            · exact hr2
            · exact hs))
        change Nat.card H ≤ Nat.card (dihedralSubgroup n)
        rw [hc, dihedralSubgroup_natCard n hn]
      · right
        right
        have hrs : r n * s n ∈ H :=
          (Subgroup.mul_mem_iff_of_index_two hH).mpr ⟨fun h => (hr h).elim,
            fun h => (hs h).elim⟩
        apply Eq.symm
        apply Subgroup.eq_of_le_of_card_ge
          ((Subgroup.closure_le H).mpr (by
            intro g hg
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
            rcases hg with rfl | rfl
            · exact hr2
            · exact hrs))
        change Nat.card H ≤ Nat.card (quaternionSubgroup n)
        rw [hc, quaternionSubgroup_natCard n hn]
  · rintro (rfl | rfl | rfl)
    · exact rotationSubgroup_index n hn
    · exact dihedralSubgroup_index n hn
    · exact quaternionSubgroup_index n hn

@[expose] def abelianizationProjection (n : ℕ) (hn : 3 ≤ n) :
    SemidihedralGroup n →* Cyclic 2 × Cyclic 2 :=
  (rotationParityHom n hn).prod (parityHom n hn)

@[simp] theorem abelianizationProjection_element (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    abelianizationProjection n hn (element n hn i e) =
      (Multiplicative.ofAdd (rotationReduction n hn i), Multiplicative.ofAdd e) := by
  simp only [abelianizationProjection, MonoidHom.prod_apply,
    rotationParityHom_element, parityHom_element]

theorem abelianizationProjection_surjective (n : ℕ) (hn : 3 ≤ n) :
    Function.Surjective (abelianizationProjection n hn) := by
  rintro ⟨a, e⟩
  refine ⟨element n hn (a.toAdd.val : ZMod (modulus n)) e.toAdd, ?_⟩
  rw [abelianizationProjection_element, map_natCast, ZMod.natCast_zmod_val]
  rfl

theorem abelianizationProjection_ker (n : ℕ) (hn : 3 ≤ n) :
    (abelianizationProjection n hn).ker = Subgroup.zpowers (r n ^ 2) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective g
    change abelianizationProjection n hn (element n hn i e) = 1 at hg
    rw [abelianizationProjection_element] at hg
    have hp : rotationReduction n hn i = 0 ∧ e = 0 := Prod.mk.inj hg
    change element n hn i e ∈ Subgroup.zpowers (r n ^ 2)
    rw [hp.2]
    exact even_rotation_mem n hn (Subgroup.zpowers (r n ^ 2))
      (Subgroup.mem_zpowers _) i ((rotationReduction_eq_zero_iff n hn i).mp hp.1)
  · apply Subgroup.zpowers_le.mpr
    change abelianizationProjection n hn (r n ^ 2) = 1
    rw [r_pow_eq_element n hn, abelianizationProjection_element, map_natCast]
    rfl

theorem element_rotation_inv (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) : (element n hn i 0)⁻¹ = element n hn (-i) 0 := by
  apply inv_eq_of_mul_eq_one_right
  rw [element_rotation_mul, add_neg_cancel, element_zero_zero]

theorem commutator_s_r (n : ℕ) (hn : 3 ≤ n) :
    ⁅s n, r n⁆ = element n hn (twist n - 1) 0 := by
  rw [commutatorElement_def, s_conj_r, r_pow_eq_element n hn,
    rotation_generator_eq_element n hn, element_rotation_inv, element_rotation_mul,
    ← twist_eq_natCast, sub_eq_add_neg]

theorem r_sq_mem_commutator (n : ℕ) (hn : 4 ≤ n) :
    r n ^ 2 ∈ commutator (SemidihedralGroup n) := by
  obtain ⟨u, hu⟩ := quarter_sub_one_isUnit n hn
  have hc : ⁅s n, r n⁆ ∈ commutator (SemidihedralGroup n) := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hp := (commutator (SemidihedralGroup n)).pow_mem hc
    (u⁻¹ : ZMod (modulus n)).val
  rw [commutator_s_r n (by omega), element_rotation_pow, nsmul_eq_mul,
    ZMod.natCast_zmod_val, twist_sub_one_eq_two_mul n hn] at hp
  have he : (u⁻¹ : ZMod (modulus n)) *
      (2 * ((2 ^ (n - 3) - 1 : ℕ) : ZMod (modulus n))) = 2 := by
    rw [← hu]
    calc
      (u⁻¹ : ZMod (modulus n)) * (2 * (u : ZMod (modulus n))) =
          2 * ((u⁻¹ : ZMod (modulus n)) * (u : ZMod (modulus n))) := by ring
      _ = 2 := by simp
  rw [he] at hp
  rw [r_pow_eq_element n (by omega) 2]
  exact hp

theorem commutator_eq_zpowers_r_sq (n : ℕ) (hn : 4 ≤ n) :
    commutator (SemidihedralGroup n) = Subgroup.zpowers (r n ^ 2) := by
  apply le_antisymm
  · rw [← abelianizationProjection_ker n (by omega)]
    exact Abelianization.commutator_subset_ker (abelianizationProjection n (by omega))
  · exact Subgroup.zpowers_le.mpr (r_sq_mem_commutator n hn)

theorem abelianizationProjection_ker_eq_commutator (n : ℕ) (hn : 4 ≤ n) :
    (abelianizationProjection n (by omega)).ker = commutator (SemidihedralGroup n) := by
  rw [abelianizationProjection_ker, commutator_eq_zpowers_r_sq n hn]

@[expose] noncomputable def abelianizationEquiv (n : ℕ) (hn : 4 ≤ n) :
    Abelianization (SemidihedralGroup n) ≃* Cyclic 2 × Cyclic 2 :=
  (QuotientGroup.quotientMulEquivOfEq
    (abelianizationProjection_ker_eq_commutator n hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (abelianizationProjection n (by omega))
      (abelianizationProjection_surjective n (by omega)))

@[simp] theorem abelianizationEquiv_of (n : ℕ) (hn : 4 ≤ n)
    (g : SemidihedralGroup n) :
    abelianizationEquiv n hn (Abelianization.of g) =
      abelianizationProjection n (by omega) g := rfl

@[simp] theorem abelianizationEquiv_r (n : ℕ) (hn : 4 ≤ n) :
    abelianizationEquiv n hn (Abelianization.of (r n)) =
      (Multiplicative.ofAdd 1, 1) := by
  rw [abelianizationEquiv_of, rotation_generator_eq_element n (by omega),
    abelianizationProjection_element, map_one]
  rfl

@[simp] theorem abelianizationEquiv_s (n : ℕ) (hn : 4 ≤ n) :
    abelianizationEquiv n hn (Abelianization.of (s n)) =
      (1, Multiplicative.ofAdd 1) := by
  rw [abelianizationEquiv_of, s_eq_element n (by omega),
    abelianizationProjection_element, map_zero]
  rfl

theorem abelianization_natCard (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (Abelianization (SemidihedralGroup n)) = 4 := by
  rw [Nat.card_congr (abelianizationEquiv n hn).toEquiv, Nat.card_prod, cyclicTwo_natCard]

theorem commutator_index (n : ℕ) (hn : 4 ≤ n) :
    (commutator (SemidihedralGroup n)).index = 4 :=
  abelianization_natCard n hn

theorem element_mem_commutator_iff (n : ℕ) (hn : 4 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    element n (by omega) i e ∈ commutator (SemidihedralGroup n) ↔
      i.val % 2 = 0 ∧ e = 0 := by
  rw [← abelianizationProjection_ker_eq_commutator n hn]
  change abelianizationProjection n (by omega) (element n (by omega) i e) = 1 ↔ _
  rw [abelianizationProjection_element]
  change (Multiplicative.ofAdd (rotationReduction n (by omega) i),
    Multiplicative.ofAdd e) = (1, 1) ↔ _
  rw [Prod.mk.injEq]
  change rotationReduction n (by omega) i = 0 ∧ e = 0 ↔ _
  rw [rotationReduction_eq_zero_iff]

theorem derived_and_index_two (n : ℕ) (hn : 4 ≤ n) :
    commutator (SemidihedralGroup n) = Subgroup.zpowers (r n ^ 2) ∧
    (∀ H : Subgroup (SemidihedralGroup n), H.index = 2 ↔
      H = rotationSubgroup n ∨ H = dihedralSubgroup n ∨ H = quaternionSubgroup n) ∧
    rotationSubgroup n ≠ dihedralSubgroup n ∧
    rotationSubgroup n ≠ quaternionSubgroup n ∧
    dihedralSubgroup n ≠ quaternionSubgroup n ∧
    (rotationSubgroup n).Normal ∧ (dihedralSubgroup n).Normal ∧
    (quaternionSubgroup n).Normal ∧
    Nat.card (rotationSubgroup n) = modulus n ∧
    Nat.card (dihedralSubgroup n) = modulus n ∧
    Nat.card (quaternionSubgroup n) = modulus n ∧ IsCyclic (rotationSubgroup n) := by
  exact ⟨commutator_eq_zpowers_r_sq n hn, index_eq_two_iff n (by omega),
    rotationSubgroup_ne_dihedralSubgroup n (by omega),
    rotationSubgroup_ne_quaternionSubgroup n (by omega),
    dihedralSubgroup_ne_quaternionSubgroup n (by omega),
    rotationSubgroup_normal n (by omega), dihedralSubgroup_normal n (by omega),
    quaternionSubgroup_normal n (by omega), rotationSubgroup_natCard n (by omega),
    dihedralSubgroup_natCard n (by omega), quaternionSubgroup_natCard n (by omega),
    rotationSubgroup_cyclic n⟩

end CFSG.Semidihedral
