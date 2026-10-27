module

public import Mathlib
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite
public import CFSG.Assembly.OrderReductions.InvolutionGraph

public section

namespace CFSG.OrderReductions.FixedPairSylow

open scoped Pointwise

theorem fixedPoints_antitone {group points : Type*} [Group group]
    [MulAction group points] {smaller larger : Subgroup group} (contains : smaller ≤ larger) :
    MulAction.fixedPoints larger points ⊆ MulAction.fixedPoints smaller points := by
  intro point fixed
  apply MulAction.mem_fixedPoints.mpr
  intro element
  exact MulAction.mem_fixedPoints.mp fixed ⟨element.val, contains element.property⟩

theorem normalizer_preserves_fixedPoints {group points : Type*} [Group group]
    [MulAction group points] (subgroup : Subgroup group) (element : group)
    (normalizes : element ∈ Subgroup.normalizer (subgroup : Set group))
    {point : points} (fixed : point ∈ MulAction.fixedPoints subgroup points) :
    element • point ∈ MulAction.fixedPoints subgroup points := by
  apply MulAction.mem_fixedPoints.mpr
  intro acting
  have conjugate_mem : element⁻¹ * acting.val * element ∈ subgroup :=
    (Subgroup.mem_normalizer_iff''.mp normalizes acting.val).mp acting.property
  have conjugate_fixed := MulAction.mem_fixedPoints.mp fixed
    ⟨element⁻¹ * acting.val * element, conjugate_mem⟩
  change (element⁻¹ * acting.val * element) • point = point at conjugate_fixed
  calc
    acting.val • (element • point) = element • ((element⁻¹ * acting.val * element) • point) := by
      simp only [← mul_smul]
      congr 1
      group
    _ = element • point := congrArg (fun moved => element • moved) conjugate_fixed

theorem fixed_pair_normalizer_stabilizer_le {group points : Type*} [Group group]
    [MulAction group points] (subgroup : Subgroup group) (first second : points)
    (distinct : first ≠ second)
    (fixed_pair : MulAction.fixedPoints subgroup points = {first, second}) :
    Subgroup.normalizer (subgroup : Set group) ⊓ MulAction.stabilizer group first ≤
      MulAction.stabilizer group first ⊓ MulAction.stabilizer group second := by
  intro element mem_intersection
  refine ⟨mem_intersection.2, ?_⟩
  have fixed_second : second ∈ MulAction.fixedPoints subgroup points := by
    rw [fixed_pair]
    simp
  have moved_fixed := normalizer_preserves_fixedPoints subgroup element
    mem_intersection.1 fixed_second
  rw [fixed_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at moved_fixed
  apply MulAction.mem_stabilizer_iff.mpr
  rcases moved_fixed with moved_first | moved_second
  · have fixes_first := MulAction.mem_stabilizer_iff.mp mem_intersection.2
    exact False.elim (distinct (MulAction.injective element
      (fixes_first.trans moved_first.symm)))
  · exact moved_second

theorem sylow_of_normalizer_control {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group)
    (prime_group : IsPGroup prime subgroup)
    (control : ∀ larger : Subgroup group, IsPGroup prime larger → subgroup ≤ larger →
      Subgroup.normalizer (subgroup : Set group) ⊓ larger ≤ subgroup) :
    ∃ sylow : Sylow prime group, (sylow : Subgroup group) = subgroup := by
  obtain ⟨sylow, contains⟩ := prime_group.exists_le_sylow
  have : Group.IsNilpotent (sylow : Subgroup group) := sylow.isPGroup'.isNilpotent
  have normalizer_condition := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := (sylow : Subgroup group)))
  have full : subgroup.subgroupOf (sylow : Subgroup group) = ⊤ := by
    apply normalizer_condition
    rw [← Subgroup.subgroupOf_normalizer_eq contains]
    apply le_antisymm
    · intro element normalizes
      exact Subgroup.mem_subgroupOf.mpr
        (control sylow sylow.isPGroup' contains
          ⟨Subgroup.mem_subgroupOf.mp normalizes, element.property⟩)
    · exact Subgroup.subgroupOf_mono _ subgroup.le_normalizer
  exact ⟨sylow, le_antisymm (Subgroup.subgroupOf_eq_top.mp full) contains⟩

theorem sylow_extension_of_normalizer_le {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (ambient : Subgroup group)
    (internal : Sylow prime ambient)
    (normalizer_le : Subgroup.normalizer
      ((internal : Subgroup ambient).map ambient.subtype : Set group) ≤ ambient) :
    ∃ sylow : Sylow prime group,
      (sylow : Subgroup group) = (internal : Subgroup ambient).map ambient.subtype := by
  let image := (internal : Subgroup ambient).map ambient.subtype
  have image_prime : IsPGroup prime image := internal.isPGroup'.map ambient.subtype
  apply sylow_of_normalizer_control prime image image_prime
  intro larger larger_prime contains
  let intersection := Subgroup.normalizer (image : Set group) ⊓ larger
  have intersection_le : intersection ≤ ambient := inf_le_left.trans normalizer_le
  have intersection_prime : IsPGroup prime intersection := larger_prime.to_le inf_le_right
  have internal_prime : IsPGroup prime (intersection.subgroupOf ambient) :=
    intersection_prime.of_equiv (Subgroup.subgroupOfEquivOfLe intersection_le).symm
  have internal_le : (internal : Subgroup ambient) ≤ intersection.subgroupOf ambient := by
    intro element mem_internal
    have mem_image := Subgroup.mem_map_of_mem ambient.subtype mem_internal
    exact ⟨image.le_normalizer mem_image, contains mem_image⟩
  have maximal := internal.is_maximal' internal_prime internal_le
  intro element mem_intersection
  have mem_internal : (⟨element, intersection_le mem_intersection⟩ : ambient) ∈
      intersection.subgroupOf ambient := mem_intersection
  rw [maximal] at mem_internal
  exact Subgroup.mem_map_of_mem ambient.subtype mem_internal

theorem internal_sylow_controls_normalizer {group : Type*} [Group group]
    (prime : ℕ) (ambient : Subgroup group) (internal : Sylow prime ambient)
    (larger : Subgroup group) (larger_prime : IsPGroup prime larger)
    (contains : (internal : Subgroup ambient).map ambient.subtype ≤ larger)
    (confined : Subgroup.normalizer
      ((internal : Subgroup ambient).map ambient.subtype : Set group) ⊓ larger ≤ ambient) :
    Subgroup.normalizer
      ((internal : Subgroup ambient).map ambient.subtype : Set group) ⊓ larger ≤
        (internal : Subgroup ambient).map ambient.subtype := by
  let image := (internal : Subgroup ambient).map ambient.subtype
  let intersection := Subgroup.normalizer (image : Set group) ⊓ larger
  have intersection_prime : IsPGroup prime intersection := larger_prime.to_le inf_le_right
  have internal_prime : IsPGroup prime (intersection.subgroupOf ambient) :=
    intersection_prime.of_equiv (Subgroup.subgroupOfEquivOfLe confined).symm
  have internal_le : (internal : Subgroup ambient) ≤ intersection.subgroupOf ambient := by
    intro element mem_internal
    have mem_image := Subgroup.mem_map_of_mem ambient.subtype mem_internal
    exact ⟨image.le_normalizer mem_image, contains mem_image⟩
  have maximal := internal.is_maximal' internal_prime internal_le
  intro element mem_intersection
  have mem_internal : (⟨element, confined mem_intersection⟩ : ambient) ∈
      intersection.subgroupOf ambient := mem_intersection
  rw [maximal] at mem_internal
  exact Subgroup.mem_map_of_mem ambient.subtype mem_internal

theorem sylow_in_subgroup_of_normalizer_intersection_le {group : Type*}
    [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (smaller ambient : Subgroup group) (smaller_le : smaller ≤ ambient)
    (internal : Sylow prime smaller)
    (confined : Subgroup.normalizer
      ((internal : Subgroup smaller).map smaller.subtype : Set group) ⊓ ambient ≤ smaller) :
    ∃ sylow : Sylow prime ambient,
      (sylow : Subgroup ambient).map ambient.subtype =
        (internal : Subgroup smaller).map smaller.subtype := by
  let image := (internal : Subgroup smaller).map smaller.subtype
  have image_le : image ≤ ambient := by
    intro element mem_image
    obtain ⟨original, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
    exact equal_image ▸ smaller_le original.property
  have image_prime : IsPGroup prime image := internal.isPGroup'.map smaller.subtype
  have restricted_prime : IsPGroup prime (image.subgroupOf ambient) :=
    image_prime.of_equiv (Subgroup.subgroupOfEquivOfLe image_le).symm
  obtain ⟨sylow, equal_image⟩ := sylow_of_normalizer_control prime
    (image.subgroupOf ambient) restricted_prime (by
      intro larger larger_prime contains
      rw [← Subgroup.subgroupOf_normalizer_eq image_le]
      have mapped_prime := larger_prime.map ambient.subtype
      have image_contains : image ≤ larger.map ambient.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le image_le]
        exact Subgroup.map_mono contains
      have mapped_le : larger.map ambient.subtype ≤ ambient := by
        intro element mem_image
        obtain ⟨original, _, equal_original⟩ := Subgroup.mem_map.mp mem_image
        exact equal_original ▸ original.property
      have mapped_confined : Subgroup.normalizer (image : Set group) ⊓
          larger.map ambient.subtype ≤ smaller := by
        exact (inf_le_inf_left _ mapped_le).trans confined
      have controlled := internal_sylow_controls_normalizer prime smaller internal
        (larger.map ambient.subtype) mapped_prime image_contains mapped_confined
      intro element mem_intersection
      apply Subgroup.mem_subgroupOf.mpr
      exact controlled ⟨Subgroup.mem_subgroupOf.mp mem_intersection.1,
        Subgroup.mem_map_of_mem ambient.subtype mem_intersection.2⟩)
  refine ⟨sylow, ?_⟩
  rw [equal_image]
  exact Subgroup.map_subgroupOf_eq_of_le image_le

theorem exists_sylow_fixed_pair {group points : Type*} [Group group] [Finite group]
    [MulAction group points] (prime : ℕ) [Fact (Nat.Prime prime)]
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup)
    (first second : points) (distinct : first ≠ second)
    (fixed_pair : MulAction.fixedPoints subgroup points = {first, second}) :
    ∃ first_sylow : Sylow prime (MulAction.stabilizer group first),
      ∃ second_sylow : Sylow prime (MulAction.stabilizer group second),
        let image := (first_sylow : Subgroup (MulAction.stabilizer group first)).map
          (MulAction.stabilizer group first).subtype
        subgroup ≤ image ∧ MulAction.fixedPoints image points = {first, second} ∧
          (second_sylow : Subgroup (MulAction.stabilizer group second)).map
            (MulAction.stabilizer group second).subtype = image := by
  let pair := MulAction.stabilizer group first ⊓ MulAction.stabilizer group second
  have subgroup_le : subgroup ≤ pair := by
    intro element mem_subgroup
    have fixed_first : first ∈ MulAction.fixedPoints subgroup points := by
      rw [fixed_pair]
      simp
    have fixed_second : second ∈ MulAction.fixedPoints subgroup points := by
      rw [fixed_pair]
      simp
    exact ⟨MulAction.mem_fixedPoints.mp fixed_first ⟨element, mem_subgroup⟩,
      MulAction.mem_fixedPoints.mp fixed_second ⟨element, mem_subgroup⟩⟩
  have restricted_prime : IsPGroup prime (subgroup.subgroupOf pair) :=
    prime_group.of_equiv (Subgroup.subgroupOfEquivOfLe subgroup_le).symm
  obtain ⟨internal, internal_contains⟩ := restricted_prime.exists_le_sylow
  let image := (internal : Subgroup pair).map pair.subtype
  have image_le : image ≤ pair := by
    intro element mem_image
    obtain ⟨original, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
    exact equal_image ▸ original.property
  have contains : subgroup ≤ image := by
    rw [← Subgroup.map_subgroupOf_eq_of_le subgroup_le]
    exact Subgroup.map_mono internal_contains
  have image_fixed_pair : MulAction.fixedPoints image points = {first, second} := by
    apply Set.Subset.antisymm
    · rw [← fixed_pair]
      exact fixedPoints_antitone contains
    · intro point mem_pair
      rcases Set.mem_insert_iff.mp mem_pair with equal_first | equal_second
      · subst point
        exact MulAction.mem_fixedPoints.mpr (fun element =>
          MulAction.mem_stabilizer_iff.mp (image_le element.property).1)
      · rw [Set.mem_singleton_iff] at equal_second
        subst point
        exact MulAction.mem_fixedPoints.mpr (fun element =>
          MulAction.mem_stabilizer_iff.mp (image_le element.property).2)
  have first_confined := fixed_pair_normalizer_stabilizer_le image first second
    distinct image_fixed_pair
  obtain ⟨first_sylow, first_image⟩ := sylow_in_subgroup_of_normalizer_intersection_le
    prime pair (MulAction.stabilizer group first) inf_le_left internal first_confined
  have second_confined : Subgroup.normalizer (image : Set group) ⊓
      MulAction.stabilizer group second ≤ pair := by
    have reversed := fixed_pair_normalizer_stabilizer_le image second first
      distinct.symm (image_fixed_pair.trans (Set.pair_comm first second))
    exact reversed.trans (by rw [inf_comm])
  obtain ⟨second_sylow, second_image⟩ := sylow_in_subgroup_of_normalizer_intersection_le
    prime pair (MulAction.stabilizer group second) inf_le_right internal second_confined
  refine ⟨first_sylow, second_sylow, ?_⟩
  dsimp only
  rw [first_image]
  exact ⟨contains, image_fixed_pair, second_image⟩

theorem odd_order_preserving_pair_fixes {group points : Type*} [Group group]
    [MulAction group points] (element : group) (odd_order : Odd (orderOf element))
    (first second : points) (distinct : first ≠ second)
    (preserves : ∀ point ∈ ({first, second} : Set points),
      element • point ∈ ({first, second} : Set points)) :
    element • first = first ∧ element • second = second := by
  have first_image := preserves first (by simp)
  have second_image := preserves second (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at first_image second_image
  rcases first_image with fixes_first | swaps_first
  · refine ⟨fixes_first, ?_⟩
    rcases second_image with maps_first | fixes_second
    · exact False.elim (distinct (MulAction.injective element
        (fixes_first.trans maps_first.symm)))
    · exact fixes_second
  · have swaps_second : element • second = first := by
      rcases second_image with swaps_second | fixes_second
      · exact swaps_second
      · exact False.elim (distinct (MulAction.injective element
          (swaps_first.trans fixes_second.symm)))
    have square_fixes : (element ^ 2) • first = first := by
      simp [pow_two, mul_smul, swaps_first, swaps_second]
    have even_power_fixes : ∀ exponent : ℕ, (element ^ 2) ^ exponent • first = first := by
      intro exponent
      induction exponent with
      | zero => simp
      | succ exponent induction_hypothesis =>
          rw [pow_succ', mul_smul, induction_hypothesis, square_fixes]
    obtain ⟨half, order_equal⟩ := odd_order
    have order_fixed : element ^ orderOf element • first = first := by
      rw [pow_orderOf_eq_one, one_smul]
    rw [order_equal] at order_fixed
    have power_image : element ^ (2 * half + 1) • first = second := by
      rw [pow_succ', mul_smul, pow_mul, even_power_fixes, swaps_first]
    exact False.elim (distinct (order_fixed.symm.trans power_image))

theorem exists_ambient_sylow_fixed_pair_of_odd {group points : Type*}
    [Group group] [Finite group] [MulAction group points]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup)
    (first second : points) (distinct : first ≠ second)
    (fixed_pair : MulAction.fixedPoints subgroup points = {first, second}) :
    ∃ sylow : Sylow prime group, subgroup ≤ (sylow : Subgroup group) ∧
      MulAction.fixedPoints (sylow : Subgroup group) points = {first, second} := by
  obtain ⟨first_sylow, second_sylow, contains, image_fixed, _⟩ :=
    exists_sylow_fixed_pair prime subgroup prime_group first second distinct fixed_pair
  let stabilizer := MulAction.stabilizer group first
  let image := (first_sylow : Subgroup stabilizer).map stabilizer.subtype
  have image_prime : IsPGroup prime image := first_sylow.isPGroup'.map stabilizer.subtype
  obtain ⟨sylow, equal_image⟩ := sylow_of_normalizer_control prime image image_prime (by
    intro larger larger_prime contains_image
    apply internal_sylow_controls_normalizer prime stabilizer first_sylow
      larger larger_prime contains_image
    intro element mem_intersection
    have element_order_odd : Odd (orderOf element) := by
      obtain ⟨exponent, order_equal⟩ := larger_prime.exists_orderOf_eq_pow
        ⟨element, mem_intersection.2⟩
      have ambient_order : orderOf element = prime ^ exponent :=
        (Subgroup.orderOf_coe (⟨element, mem_intersection.2⟩ : larger)).trans order_equal
      rw [ambient_order]
      exact odd_prime.pow
    apply MulAction.mem_stabilizer_iff.mpr
    apply (odd_order_preserving_pair_fixes element element_order_odd first second distinct ?_).1
    intro point mem_pair
    have point_fixed : point ∈ MulAction.fixedPoints image points := by
      rw [image_fixed]
      exact mem_pair
    have moved_fixed := normalizer_preserves_fixedPoints image element
      mem_intersection.1 point_fixed
    rwa [image_fixed] at moved_fixed)
  refine ⟨sylow, ?_⟩
  rw [equal_image]
  exact ⟨contains, image_fixed⟩

theorem fixedPoints_map_subtype {group points : Type*} [Group group]
    [MulAction group points] (ambient : Subgroup group) (subgroup : Subgroup ambient) :
    MulAction.fixedPoints (subgroup.map ambient.subtype) points =
      MulAction.fixedPoints subgroup points := by
  ext point
  constructor
  · intro fixed
    apply MulAction.mem_fixedPoints.mpr
    intro element
    exact MulAction.mem_fixedPoints.mp fixed
      ⟨element.val.val, Subgroup.mem_map_of_mem ambient.subtype element.property⟩
  · intro fixed
    apply MulAction.mem_fixedPoints.mpr
    intro element
    obtain ⟨original, mem_original, equal_image⟩ := Subgroup.mem_map.mp element.property
    have original_fixed := MulAction.mem_fixedPoints.mp fixed ⟨original, mem_original⟩
    change original.val • point = point at original_fixed
    change element.val • point = point
    rwa [← equal_image]

theorem conjugate_smul_mem_fixedPoints {group points : Type*} [Group group]
    [MulAction group points] (subgroup : Subgroup group) (element : group)
    {point : points} (fixed : point ∈ MulAction.fixedPoints subgroup points) :
    element • point ∈ MulAction.fixedPoints
      (subgroup.map (MulAut.conj element).toMonoidHom) points := by
  apply MulAction.mem_fixedPoints.mpr
  intro acting
  obtain ⟨original, mem_original, equal_conjugate⟩ := Subgroup.mem_map.mp acting.property
  have original_fixed := MulAction.mem_fixedPoints.mp fixed ⟨original, mem_original⟩
  change original • point = point at original_fixed
  change acting.val • (element • point) = element • point
  rw [← equal_conjugate]
  change (element * original * element⁻¹) • (element • point) = element • point
  simp only [mul_smul, inv_smul_smul, original_fixed]

theorem sylow_smul_mem_fixedPoints {group points : Type*} [Group group]
    [MulAction group points] (prime : ℕ) (sylow : Sylow prime group) (element : group)
    {point : points} (fixed : point ∈ MulAction.fixedPoints (sylow : Subgroup group) points) :
    element • point ∈ MulAction.fixedPoints
      ((element • sylow : Sylow prime group) : Subgroup group) points := by
  have conjugate_eq : ((element • sylow : Sylow prime group) : Subgroup group) =
      (sylow : Subgroup group).map (MulAut.conj element).toMonoidHom := by
    ext acting
    change acting ∈ ((element • sylow : Sylow prime group) : Set group) ↔ _
    rw [Sylow.coe_smul]
    rfl
  rw [conjugate_eq]
  exact conjugate_smul_mem_fixedPoints (sylow : Subgroup group) element fixed

theorem pair_realization_stabilizer_transitive {group points : Type*}
    [Group group] [Finite group] [MulAction group points]
    (prime : ℕ) [Fact (Nat.Prime prime)] (base : points)
    (realizes : ∀ other : points, base ≠ other →
      ∃ subgroup : Subgroup group, IsPGroup prime subgroup ∧
        MulAction.fixedPoints subgroup points = {base, other})
    (first second : points) (first_distinct : base ≠ first) (second_distinct : base ≠ second) :
    ∃ element : MulAction.stabilizer group base, element.val • first = second := by
  obtain ⟨first_group, first_prime, first_fixed⟩ := realizes first first_distinct
  obtain ⟨second_group, second_prime, second_fixed⟩ := realizes second second_distinct
  obtain ⟨first_sylow, _, _, first_image_fixed, _⟩ := exists_sylow_fixed_pair prime
    first_group first_prime base first first_distinct first_fixed
  obtain ⟨second_sylow, _, _, second_image_fixed, _⟩ := exists_sylow_fixed_pair prime
    second_group second_prime base second second_distinct second_fixed
  rw [fixedPoints_map_subtype] at first_image_fixed second_image_fixed
  obtain ⟨element, conjugates⟩ := MulAction.exists_smul_eq
    (MulAction.stabilizer group base) first_sylow second_sylow
  have first_is_fixed : first ∈ MulAction.fixedPoints
      (first_sylow : Subgroup (MulAction.stabilizer group base)) points := by
    rw [first_image_fixed]
    simp
  have moved_fixed := sylow_smul_mem_fixedPoints prime first_sylow element first_is_fixed
  rw [conjugates, second_image_fixed] at moved_fixed
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at moved_fixed
  refine ⟨element, ?_⟩
  rcases moved_fixed with maps_base | maps_second
  · have fixes_base := MulAction.mem_stabilizer_iff.mp element.property
    exact False.elim (first_distinct (MulAction.injective element.val
      (fixes_base.trans maps_base.symm)))
  · exact maps_second

theorem two_pretransitive_of_stabilizer_transitive_and_moves {group points : Type*}
    [Group group] [MulAction group points] (base : points)
    (stabilizer_transitive : ∀ first second : points, base ≠ first → base ≠ second →
      ∃ element : MulAction.stabilizer group base, element.val • first = second)
    (moves : ∃ element : group, element • base ≠ base) :
    MulAction.IsMultiplyPretransitive group points 2 := by
  obtain ⟨moving, moved⟩ := moves
  have base_transitive : ∀ point : points, ∃ element : group, element • base = point := by
    intro point
    by_cases equal_base : base = point
    · exact ⟨1, by simpa using equal_base⟩
    · obtain ⟨element, sends⟩ := stabilizer_transitive (moving • base) point
        moved.symm equal_base
      exact ⟨element.val * moving, by simpa only [mul_smul] using sends⟩
  apply MulAction.is_two_pretransitive_iff.mpr
  intro first second third fourth first_distinct third_distinct
  obtain ⟨first_mover, first_image⟩ := base_transitive first
  obtain ⟨third_mover, third_image⟩ := base_transitive third
  have second_preimage_distinct : base ≠ first_mover⁻¹ • second := by
    intro equal_preimage
    apply first_distinct
    calc
      first = first_mover • base := first_image.symm
      _ = second := by rw [equal_preimage, smul_inv_smul]
  have fourth_preimage_distinct : base ≠ third_mover⁻¹ • fourth := by
    intro equal_preimage
    apply third_distinct
    calc
      third = third_mover • base := third_image.symm
      _ = fourth := by rw [equal_preimage, smul_inv_smul]
  obtain ⟨middle, middle_image⟩ := stabilizer_transitive
    (first_mover⁻¹ • second) (third_mover⁻¹ • fourth)
    second_preimage_distinct fourth_preimage_distinct
  refine ⟨third_mover * middle.val * first_mover⁻¹, ?_, ?_⟩
  · have middle_fixes := MulAction.mem_stabilizer_iff.mp middle.property
    rw [mul_smul, mul_smul, ← first_image, inv_smul_smul, middle_fixes, third_image]
  · rw [mul_smul, mul_smul, middle_image, smul_inv_smul]

theorem pair_realization_two_pretransitive {group points : Type*}
    [Group group] [Finite group] [MulAction group points]
    (prime : ℕ) [Fact (Nat.Prime prime)] (base : points)
    (realizes : ∀ other : points, base ≠ other →
      ∃ subgroup : Subgroup group, IsPGroup prime subgroup ∧
        MulAction.fixedPoints subgroup points = {base, other})
    (moves : ∃ element : group, element • base ≠ base) :
    MulAction.IsMultiplyPretransitive group points 2 := by
  exact two_pretransitive_of_stabilizer_transitive_and_moves base
    (pair_realization_stabilizer_transitive prime base realizes) moves

theorem all_pairs_realization_two_pretransitive {group points : Type*}
    [Group group] [Finite group] [MulAction group points] [Finite points]
    (prime : ℕ) [Fact (Nat.Prime prime)] (degree : 3 ≤ Nat.card points)
    (realizes : ∀ first second : points, first ≠ second →
      ∃ subgroup : Subgroup group, IsPGroup prime subgroup ∧
        MulAction.fixedPoints subgroup points = {first, second}) :
    MulAction.IsMultiplyPretransitive group points 2 := by
  classical
  let := Fintype.ofFinite points
  have degree_gt : 2 < Fintype.card points := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨base, first, second, base_first, base_second, first_second⟩ :=
    Fintype.two_lt_card_iff.mp degree_gt
  apply pair_realization_two_pretransitive prime base (realizes base)
  by_contra no_moves
  push Not at no_moves
  obtain ⟨subgroup, _, fixed_pair⟩ := realizes first second first_second
  have fixed_base : base ∈ MulAction.fixedPoints subgroup points :=
    MulAction.mem_fixedPoints.mpr (fun element => no_moves element.val)
  rw [fixed_pair] at fixed_base
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at fixed_base
  exact fixed_base.elim base_first base_second

theorem sylow_smul_subgroup_eq {group : Type*} [Group group]
    (prime : ℕ) (sylow : Sylow prime group) (element : group) :
    ((element • sylow : Sylow prime group) : Subgroup group) =
      (sylow : Subgroup group).map (MulAut.conj element).toMonoidHom := by
  ext acting
  change acting ∈ ((element • sylow : Sylow prime group) : Set group) ↔ _
  rw [Sylow.coe_smul]
  rfl

theorem sylow_subtype_smul_image {group : Type*} [Group group]
    (prime : ℕ) (ambient : Subgroup group) (sylow : Sylow prime ambient) (element : ambient) :
    (((element • sylow : Sylow prime ambient) : Subgroup ambient).map ambient.subtype) =
      ((sylow : Subgroup ambient).map ambient.subtype).map
        (MulAut.conj element.val).toMonoidHom := by
  have intertwines : ambient.subtype.comp (MulAut.conj element).toMonoidHom =
      (MulAut.conj element.val).toMonoidHom.comp ambient.subtype := by
    ext acting
    rfl
  rw [sylow_smul_subgroup_eq, Subgroup.map_map, intertwines, ← Subgroup.map_map]

theorem exists_fixed_pair_orbit_flip {group points : Type*} [Group group] [Finite group]
    [MulAction group points] (prime : ℕ) [Fact (Nat.Prime prime)]
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup)
    (first second : points) (distinct : first ≠ second)
    (fixed_pair : MulAction.fixedPoints subgroup points = {first, second})
    (same_orbit : ∃ element : group, element • first = second) :
    ∃ element : group, element • first = second ∧ element • second = first := by
  obtain ⟨first_sylow, second_sylow, _, image_fixed, same_image⟩ :=
    exists_sylow_fixed_pair prime subgroup prime_group first second distinct fixed_pair
  obtain ⟨mover, moves⟩ := same_orbit
  let stabilizer_equiv : MulAction.stabilizer group first ≃*
      MulAction.stabilizer group second := MulAction.stabilizerEquivStabilizer moves.symm
  have stabilizer_surjective : Function.Surjective stabilizer_equiv.toMonoidHom := by
    intro target
    obtain ⟨source, equal_image⟩ := stabilizer_equiv.surjective target
    exact ⟨source, equal_image⟩
  let transported : Sylow prime (MulAction.stabilizer group second) :=
    Sylow.mapSurjective (f := stabilizer_equiv.toMonoidHom)
      stabilizer_surjective first_sylow
  have transported_image :
      (transported : Subgroup (MulAction.stabilizer group second)).map
        (MulAction.stabilizer group second).subtype =
      ((first_sylow : Subgroup (MulAction.stabilizer group first)).map
        (MulAction.stabilizer group first).subtype).map (MulAut.conj mover).toMonoidHom := by
    have intertwines : (MulAction.stabilizer group second).subtype.comp
        stabilizer_equiv.toMonoidHom = (MulAut.conj mover).toMonoidHom.comp
          (MulAction.stabilizer group first).subtype := by
      ext element
      exact MulAction.stabilizerEquivStabilizer_apply moves.symm element
    dsimp only [transported]
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, intertwines, ← Subgroup.map_map]
  obtain ⟨adjustment, conjugates⟩ := MulAction.exists_smul_eq
    (MulAction.stabilizer group second) transported second_sylow
  let image := (first_sylow : Subgroup (MulAction.stabilizer group first)).map
    (MulAction.stabilizer group first).subtype
  let flipper := adjustment.val * mover
  have adjustment_image := congrArg
    (fun current : Sylow prime (MulAction.stabilizer group second) =>
      (current : Subgroup (MulAction.stabilizer group second)).map
        (MulAction.stabilizer group second).subtype) conjugates
  rw [sylow_subtype_smul_image, transported_image, same_image, Subgroup.map_map]
    at adjustment_image
  have composite_conjugation : (MulAut.conj adjustment.val).toMonoidHom.comp
      (MulAut.conj mover).toMonoidHom = (MulAut.conj flipper).toMonoidHom := by
    ext element
    change adjustment.val * (mover * element * mover⁻¹) * adjustment.val⁻¹ =
      (adjustment.val * mover) * element * (adjustment.val * mover)⁻¹
    group
  rw [composite_conjugation] at adjustment_image
  have normalizes : flipper ∈ Subgroup.normalizer (image : Set group) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact adjustment_image
  have sends_first : flipper • first = second := by
    rw [show flipper = adjustment.val * mover from rfl, mul_smul, moves]
    exact MulAction.mem_stabilizer_iff.mp adjustment.property
  have second_fixed : second ∈ MulAction.fixedPoints image points := by
    rw [image_fixed]
    simp
  have moved_fixed := normalizer_preserves_fixedPoints image flipper normalizes second_fixed
  rw [image_fixed] at moved_fixed
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at moved_fixed
  refine ⟨flipper, sends_first, ?_⟩
  rcases moved_fixed with sends_second | fixes_second
  · exact sends_second
  · exact False.elim (distinct (MulAction.injective flipper
      (sends_first.trans fixes_second.symm)))

theorem exists_larger_prime_subgroup_in_normalizer {group : Type*}
    [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup)
    (not_sylow : ¬ ∃ sylow : Sylow prime group, (sylow : Subgroup group) = subgroup) :
    ∃ larger : Subgroup group, IsPGroup prime larger ∧ subgroup < larger ∧
      larger ≤ Subgroup.normalizer (subgroup : Set group) := by
  obtain ⟨sylow, contains⟩ := prime_group.exists_le_sylow
  let internal := subgroup.subgroupOf (sylow : Subgroup group)
  have not_full : internal ≠ ⊤ := by
    intro full
    exact not_sylow ⟨sylow, le_antisymm (Subgroup.subgroupOf_eq_top.mp full) contains⟩
  have : Group.IsNilpotent (sylow : Subgroup group) := sylow.isPGroup'.isNilpotent
  have internal_lt : internal < Subgroup.normalizer (internal : Set (sylow : Subgroup group)) :=
    Group.normalizerCondition_of_isNilpotent internal (lt_top_iff_ne_top.mpr not_full)
  let normalizer := Subgroup.normalizer (internal : Set (sylow : Subgroup group))
  let larger := normalizer.map (sylow : Subgroup group).subtype
  have larger_prime : IsPGroup prime larger :=
    (sylow.isPGroup'.to_subgroup normalizer).map (sylow : Subgroup group).subtype
  have larger_le : larger ≤ Subgroup.normalizer (subgroup : Set group) := by
    change (Subgroup.normalizer (subgroup.subgroupOf
      (sylow : Subgroup group) : Set (sylow : Subgroup group))).map
        (sylow : Subgroup group).subtype ≤ _
    rw [← Subgroup.subgroupOf_normalizer_eq contains,
      Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have subgroup_le : subgroup ≤ larger := by
    rw [← Subgroup.map_subgroupOf_eq_of_le contains]
    exact Subgroup.map_mono internal_lt.le
  refine ⟨larger, larger_prime, lt_of_le_of_ne subgroup_le ?_, larger_le⟩
  intro equal_larger
  have mapped_equal : internal.map (sylow : Subgroup group).subtype =
      normalizer.map (sylow : Subgroup group).subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le contains]
    exact equal_larger
  exact internal_lt.ne (Subgroup.map_injective Subtype.val_injective mapped_equal)

theorem exists_larger_prime_subgroup_in_normalizer_within {group : Type*}
    [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (subgroup ambient : Subgroup group) (contains : subgroup ≤ ambient)
    (prime_group : IsPGroup prime subgroup)
    (not_sylow : ¬ ∃ sylow : Sylow prime ambient,
      (sylow : Subgroup ambient).map ambient.subtype = subgroup) :
    ∃ larger : Subgroup group, IsPGroup prime larger ∧ subgroup < larger ∧
      larger ≤ Subgroup.normalizer (subgroup : Set group) ⊓ ambient := by
  have restricted_prime : IsPGroup prime (subgroup.subgroupOf ambient) :=
    prime_group.of_equiv (Subgroup.subgroupOfEquivOfLe contains).symm
  have restricted_not_sylow : ¬ ∃ sylow : Sylow prime ambient,
      (sylow : Subgroup ambient) = subgroup.subgroupOf ambient := by
    rintro ⟨sylow, equal_subgroup⟩
    apply not_sylow
    refine ⟨sylow, ?_⟩
    rw [equal_subgroup, Subgroup.map_subgroupOf_eq_of_le contains]
  obtain ⟨internal, internal_prime, strictly_larger, normalizes⟩ :=
    exists_larger_prime_subgroup_in_normalizer prime (subgroup.subgroupOf ambient)
      restricted_prime restricted_not_sylow
  let larger := internal.map ambient.subtype
  have larger_prime : IsPGroup prime larger := internal_prime.map ambient.subtype
  have larger_le : larger ≤ Subgroup.normalizer (subgroup : Set group) ⊓ ambient := by
    have mapped_le := Subgroup.map_mono (f := ambient.subtype) normalizes
    rw [← Subgroup.subgroupOf_normalizer_eq contains, Subgroup.subgroupOf_map_subtype]
      at mapped_le
    exact mapped_le
  have subgroup_le : subgroup ≤ larger := by
    rw [← Subgroup.map_subgroupOf_eq_of_le contains]
    exact Subgroup.map_mono strictly_larger.le
  refine ⟨larger, larger_prime, lt_of_le_of_ne subgroup_le ?_, larger_le⟩
  intro equal_larger
  have mapped_equal : (subgroup.subgroupOf ambient).map ambient.subtype =
      internal.map ambient.subtype := by
    rw [Subgroup.map_subgroupOf_eq_of_le contains]
    exact equal_larger
  exact strictly_larger.ne (Subgroup.map_injective Subtype.val_injective mapped_equal)

theorem power_preserves_pair {group points : Type*} [Group group] [MulAction group points]
    (element : group) (first second : points)
    (preserves : ∀ point ∈ ({first, second} : Set points),
      element • point ∈ ({first, second} : Set points))
    (exponent : ℕ) {point : points} (mem_pair : point ∈ ({first, second} : Set points)) :
    element ^ exponent • point ∈ ({first, second} : Set points) := by
  induction exponent with
  | zero => simpa using mem_pair
  | succ exponent induction_hypothesis =>
      rw [pow_succ', mul_smul]
      exact preserves _ induction_hypothesis

theorem involution_power_flips_pair {group points : Type*}
    [Group group] [Finite group] [MulAction group points]
    (unique_fixed : ∀ involution : CFSG.OrderReductions.InvolutionGraph.Involution group,
      ∀ first second : points, involution.val • first = first →
        involution.val • second = second → first = second)
    (element : group) (first second : points) (distinct : first ≠ second)
    (first_moves : element • first = second) (second_moves : element • second = first) :
    ∃ exponent : ℕ, orderOf (element ^ exponent) = 2 ∧
      element ^ exponent • first = second ∧ element ^ exponent • second = first := by
  have preserves : ∀ point ∈ ({first, second} : Set points),
      element • point ∈ ({first, second} : Set points) := by
    intro point mem_pair
    rcases Set.mem_insert_iff.mp mem_pair with equal_first | equal_second
    · subst point
      rw [first_moves]
      simp
    · rw [Set.mem_singleton_iff] at equal_second
      subst point
      rw [second_moves]
      simp
  have even_order : Even (orderOf element) := by
    apply Nat.not_odd_iff_even.mp
    intro odd_order
    have fixes_first :=
      (odd_order_preserving_pair_fixes element odd_order first second distinct preserves).1
    exact distinct (fixes_first.symm.trans first_moves)
  let exponent := orderOf element / 2
  have power_order : orderOf (element ^ exponent) = 2 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos element)) even_order.two_dvd
  have first_image := power_preserves_pair element first second preserves exponent
    (point := first) (by simp)
  have second_image := power_preserves_pair element first second preserves exponent
    (point := second) (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at first_image second_image
  refine ⟨exponent, power_order, ?_, ?_⟩
  · rcases first_image with fixes_first | moves_first
    · rcases second_image with moves_second | fixes_second
      · exact False.elim (distinct (MulAction.injective (element ^ exponent)
          (fixes_first.trans moves_second.symm)))
      · exact False.elim (distinct (unique_fixed ⟨element ^ exponent, power_order⟩
          first second fixes_first fixes_second))
    · exact moves_first
  · rcases second_image with moves_second | fixes_second
    · exact moves_second
    · rcases first_image with fixes_first | moves_first
      · exact False.elim (distinct (unique_fixed ⟨element ^ exponent, power_order⟩
          first second fixes_first fixes_second))
      · exact False.elim (distinct (MulAction.injective (element ^ exponent)
          (moves_first.trans fixes_second.symm)))

end CFSG.OrderReductions.FixedPairSylow
