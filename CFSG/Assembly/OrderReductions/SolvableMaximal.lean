module

public import CFSG.Assembly.OrderReductions.StrongEmbeddingInheritance
public import CFSG.Assembly.OrderReductions.OddKernelInvolutions
public import CFSG.Assembly.OrderReductions.PrimeRegular

public section

namespace CFSG.OrderReductions.SolvableMaximal

open CFSG.OrderReductions.InvolutionGraph

theorem exists_abelian_normal {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (nontrivial : (⊤ : Subgroup group) ≠ ⊥) :
    ∃ normal : Subgroup group, normal.Normal ∧ normal ≠ ⊥ ∧ IsMulCommutative normal := by
  obtain ⟨normal, _, minimal⟩ := Finite.exists_le_minimal
    (p := fun subgroup : Subgroup group => subgroup.Normal ∧ subgroup ≠ ⊥)
    (a := ⊤) ⟨inferInstance, nontrivial⟩
  have : normal.Normal := minimal.prop.1
  refine ⟨normal, inferInstance, minimal.prop.2, ?_⟩
  apply Subgroup.commutator_self_eq_bot_iff.mp
  by_contra commutator_nontrivial
  have equal := minimal.eq_of_le
    ⟨inferInstance, commutator_nontrivial⟩ (Subgroup.commutator_le_left normal normal)
  exact (Group.IsSolvable.commutator_lt_of_ne_bot minimal.prop.2).ne equal

theorem centralizer_intersection_le_core {group : Type*} [Group group]
    (subgroup normal : Subgroup group) [normal.Normal]
    (generates : normal ⊔ subgroup = ⊤) :
    subgroup ⊓ Subgroup.centralizer (normal : Set group) ≤ subgroup.normalCore := by
  let intersection := subgroup ⊓ Subgroup.centralizer (normal : Set group)
  have : intersection.Normal := by
    constructor
    intro element element_mem conjugator
    obtain ⟨first, first_mem, second, second_mem, product_eq⟩ :=
      Subgroup.mem_sup_of_normal_left.mp (generates ▸ Subgroup.mem_top conjugator)
    have conjugate_mem : second * element * second⁻¹ ∈ intersection :=
      ⟨subgroup.mul_mem (subgroup.mul_mem second_mem element_mem.1)
          (subgroup.inv_mem second_mem),
        (inferInstance : (Subgroup.centralizer (normal : Set group)).Normal).conj_mem
          element element_mem.2 second⟩
    have commuting := Subgroup.mem_centralizer_iff.mp conjugate_mem.2 first first_mem
    have conjugate_eq : conjugator * element * conjugator⁻¹ = second * element * second⁻¹ := by
      rw [← product_eq, mul_inv_rev]
      calc
        first * second * element * (second⁻¹ * first⁻¹) =
            first * (second * element * second⁻¹) * first⁻¹ := by group
        _ = second * element * second⁻¹ := by
          rw [commuting, mul_assoc, mul_inv_cancel, mul_one]
    exact conjugate_eq ▸ conjugate_mem
  exact Subgroup.normal_le_normalCore.mpr inf_le_left

theorem exists_core_free_abelian_complement {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (subgroup : Subgroup group) (maximal : IsCoatom subgroup)
    (core_free : subgroup.normalCore = ⊥) :
    ∃ normal : Subgroup group, normal.Normal ∧ normal ≠ ⊥ ∧
      IsMulCommutative normal ∧ normal ⊔ subgroup = ⊤ ∧
      normal ⊓ subgroup = ⊥ ∧ subgroup ⊓ Subgroup.centralizer (normal : Set group) = ⊥ := by
  have nontrivial : (⊤ : Subgroup group) ≠ ⊥ := by
    intro top_eq_bot
    exact maximal.ne_top (eq_top_iff.mpr (top_eq_bot ▸ bot_le))
  obtain ⟨normal, normal_normal, normal_nontrivial, normal_abelian⟩ :=
    exists_abelian_normal nontrivial
  have : normal.Normal := normal_normal
  have not_contained : ¬ normal ≤ subgroup := by
    intro contains
    have contained_core := Subgroup.normal_le_normalCore.mpr contains
    rw [core_free] at contained_core
    exact normal_nontrivial (le_bot_iff.mp contained_core)
  have strict : subgroup < normal ⊔ subgroup :=
    lt_of_le_of_ne le_sup_right (by
      intro equal
      exact not_contained (equal ▸ le_sup_left))
  have generates := maximal.lt_iff.mp strict
  have centralizer_bot : subgroup ⊓ Subgroup.centralizer (normal : Set group) = ⊥ := by
    apply le_bot_iff.mp
    rw [← core_free]
    exact centralizer_intersection_le_core subgroup normal generates
  refine ⟨normal, normal_normal, normal_nontrivial, normal_abelian, generates, ?_, centralizer_bot⟩
  apply le_bot_iff.mp
  rw [← centralizer_bot]
  exact le_inf inf_le_right (inf_le_left.trans
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr normal_abelian))

theorem involution_inverts_normal {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (normal : Subgroup group) [normal.Normal] (disjoint : normal ⊓ subgroup = ⊥)
    (involution : Involution group) (mem_subgroup : involution.val ∈ subgroup)
    (element : normal) : involution.val * element.val * involution.val⁻¹ = element.val⁻¹ := by
  let automorphism : MulAut normal := MulAut.conjNormal involution.val
  have involutive : Function.Involutive automorphism := by
    intro element
    apply Subtype.ext
    change (MulAut.conj involution.val) ((MulAut.conj involution.val) element.val) = element.val
    exact CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive involution element.val
  have fixed_free : MonoidHom.FixedPointFree automorphism := by
    intro element fixed
    have fixed_values : involution.val * element.val * involution.val⁻¹ = element.val :=
      congrArg Subtype.val fixed
    have mem_centralizer : element.val ∈ Subgroup.centralizer ({involution.val} : Set group) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro other other_mem
      have other_eq : other = involution.val := by simpa only [Set.mem_singleton_iff] using other_mem
      rw [other_eq]
      exact mul_inv_eq_iff_eq_mul.mp fixed_values
    have mem_intersection : element.val ∈ normal ⊓ subgroup :=
      ⟨element.property, stronglyEmbedded_centralizer_le subgroup strong involution mem_subgroup
        mem_centralizer⟩
    rw [disjoint, Subgroup.mem_bot] at mem_intersection
    exact Subtype.ext mem_intersection
  exact congrArg Subtype.val
    (congrFun (fixed_free.coe_eq_inv_of_involutive involutive) element)

theorem core_free_involutions_unique {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (maximal : IsCoatom subgroup) (core_free : subgroup.normalCore = ⊥)
    (first second : Involution group)
    (first_mem : first.val ∈ subgroup) (second_mem : second.val ∈ subgroup) : first = second := by
  obtain ⟨normal, normal_normal, _, _, _, disjoint, centralizer_bot⟩ :=
    exists_core_free_abelian_complement subgroup maximal core_free
  have : normal.Normal := normal_normal
  have product_centralizes : first.val * second.val ∈ Subgroup.centralizer (normal : Set group) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro element element_mem
    have first_inverts := involution_inverts_normal subgroup strong normal disjoint first first_mem
      (⟨element, element_mem⟩ : normal)
    have second_inverts := involution_inverts_normal subgroup strong normal disjoint second second_mem
      (⟨element, element_mem⟩ : normal)
    have product_fixed : (MulAut.conj (first.val * second.val)) element = element := by
      rw [map_mul, MulAut.mul_apply]
      rw [show (MulAut.conj second.val) element = element⁻¹ from second_inverts, map_inv,
        show (MulAut.conj first.val) element = element⁻¹ from first_inverts, inv_inv]
    exact (mul_inv_eq_iff_eq_mul.mp product_fixed).symm
  have product_one : first.val * second.val = 1 := by
    have mem_intersection : first.val * second.val ∈
        subgroup ⊓ Subgroup.centralizer (normal : Set group) :=
      ⟨subgroup.mul_mem first_mem second_mem, product_centralizes⟩
    rwa [centralizer_bot, Subgroup.mem_bot] at mem_intersection
  apply Subtype.ext
  exact (mul_eq_one_iff_eq_inv.mp product_one).trans (by
    have square := pow_orderOf_eq_one second.val
    rw [second.property, pow_two] at square
    exact inv_eq_of_mul_eq_one_right square)

theorem maximal_map_of_kernel_le {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (subgroup : Subgroup source) (maximal : IsCoatom subgroup)
    (kernel_le : homomorphism.ker ≤ subgroup) : IsCoatom (subgroup.map homomorphism) := by
  have preimage_eq := Subgroup.comap_map_eq_self kernel_le
  constructor
  · intro image_top
    rw [image_top, Subgroup.comap_top] at preimage_eq
    exact maximal.ne_top preimage_eq.symm
  · intro larger strict
    have strict_preimage : subgroup < larger.comap homomorphism := by
      rw [← preimage_eq]
      refine lt_of_le_of_ne (Subgroup.comap_mono strict.le) ?_
      intro equal
      exact strict.ne (Subgroup.comap_injective surjective equal)
    have top_preimage := maximal.lt_iff.mp strict_preimage
    exact Subgroup.comap_injective surjective
      (top_preimage.trans (Subgroup.comap_top homomorphism).symm)

theorem quotient_core_free {group : Type*} [Group group]
    (subgroup : Subgroup group) :
    (subgroup.map (QuotientGroup.mk' subgroup.normalCore)).normalCore = ⊥ := by
  let projection := QuotientGroup.mk' subgroup.normalCore
  let image := subgroup.map projection
  let preimage := image.normalCore.comap projection
  have : preimage.Normal := inferInstance
  have kernel_le : projection.ker ≤ subgroup := by
    rw [QuotientGroup.ker_mk']
    exact subgroup.normalCore_le
  have preimage_le : preimage ≤ subgroup := by
    have contains := Subgroup.comap_mono (f := projection) image.normalCore_le
    rwa [Subgroup.comap_map_eq_self kernel_le] at contains
  have preimage_core : preimage ≤ subgroup.normalCore :=
    Subgroup.normal_le_normalCore.mpr preimage_le
  apply le_bot_iff.mp
  intro element element_mem
  obtain ⟨original, equal_image⟩ := QuotientGroup.mk'_surjective subgroup.normalCore element
  have original_mem : original ∈ preimage := by
    change projection original ∈ image.normalCore
    rwa [equal_image]
  have original_kernel : original ∈ projection.ker := by
    rw [QuotientGroup.ker_mk']
    exact preimage_core original_mem
  change element = 1
  rw [← equal_image]
  exact original_kernel

theorem core_free_pair_centralizer {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (maximal : IsCoatom subgroup) (core_free : subgroup.normalCore = ⊥)
    (outside : Involution group) (outside_mem : outside.val ∉ subgroup) :
    subgroup ⊓ subgroup.map (MulAut.conj outside.val).toMonoidHom =
      subgroup ⊓ Subgroup.centralizer ({outside.val} : Set group) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 strong.2.1.two_dvd
  let inside : Involution group :=
    ⟨element.val, (Subgroup.orderOf_coe element).trans element_order⟩
  have inside_mem : inside.val ∈ subgroup := element.property
  have fixed_inside (acting : group) (acting_mem : acting ∈ subgroup) :
      acting • inside = inside := by
    apply core_free_involutions_unique subgroup strong maximal core_free
    · exact CFSG.OrderReductions.OutsideInvolutions.conjugate_mem_of_mem subgroup acting inside acting_mem inside_mem
    · exact inside_mem
  apply le_antisymm
  · intro acting acting_mem
    have outside_inverse : outside.val⁻¹ = outside.val := inv_eq_self_of_orderOf_eq_two outside.property
    have reflected_mem : outside.val * acting * outside.val⁻¹ ∈ subgroup := by
      obtain ⟨original, original_mem, image_eq⟩ := Subgroup.mem_map.mp acting_mem.2
      have equal : (MulAut.conj outside.val) acting = original := by
        rw [← image_eq]
        exact CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive outside original
      change (MulAut.conj outside.val) acting ∈ subgroup
      rwa [equal]
    have acting_fixes_image : acting • (outside.val • inside) = outside.val • inside := by
      have reflected_fixes := fixed_inside (outside.val * acting * outside.val⁻¹) reflected_mem
      have transported := congrArg (fun vertex : Involution group => outside.val • vertex) reflected_fixes
      rw [← mul_smul] at transported
      have product_eq : outside.val * (outside.val * acting * outside.val⁻¹) = acting * outside.val := by
        have square : outside.val * outside.val = 1 := by
          have power := pow_orderOf_eq_one outside.val
          rwa [outside.property, pow_two] at power
        rw [← mul_assoc, ← mul_assoc, square, one_mul, outside_inverse]
      rw [product_eq, mul_smul] at transported
      exact transported
    have reflected_moves : (acting • outside).val • inside = outside.val • inside := by
      rw [involution_smul_val, mul_smul, mul_smul,
        fixed_inside acting⁻¹ (subgroup.inv_mem acting_mem.1)]
      exact acting_fixes_image
    have image_outside : (outside.val • inside).val ∉ subgroup := by
      intro image_mem
      exact outside_mem (stronglyEmbedded_involution_conjugator_mem subgroup strong inside
        inside_mem outside.val image_mem)
    obtain ⟨unique, _, uniqueness⟩ :=
      CFSG.OrderReductions.OutsideInvolutions.unique_outside_conjugator subgroup strong inside (outside.val • inside)
        inside_mem image_outside
    have equal_involutions : acting • outside = outside :=
      (uniqueness (acting • outside) reflected_moves).trans
        (uniqueness outside rfl).symm
    refine ⟨acting_mem.1, ?_⟩
    rw [← involution_stabilizer_eq_centralizer]
    exact MulAction.mem_stabilizer_iff.mpr equal_involutions
  · intro acting acting_mem
    refine ⟨acting_mem.1, Subgroup.mem_map.mpr ⟨acting, acting_mem.1, ?_⟩⟩
    have commutes := Subgroup.mem_centralizer_iff.mp acting_mem.2 outside.val (Set.mem_singleton _)
    change outside.val * acting * outside.val⁻¹ = acting
    rw [commutes, mul_assoc, mul_inv_cancel, mul_one]

theorem conjugate_centralizer_le {group : Type*} [Group group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (conjugator : group) (involution : Involution group)
    (mem_conjugate : involution.val ∈ subgroup.map (MulAut.conj conjugator).toMonoidHom) :
    Subgroup.centralizer ({involution.val} : Set group) ≤
      subgroup.map (MulAut.conj conjugator).toMonoidHom := by
  let original := conjugator⁻¹ • involution
  have original_mem : original.val ∈ subgroup := by
    rw [Subgroup.mem_map_equiv] at mem_conjugate
    simpa only [original, involution_smul_val, MulAut.conj_symm_apply, inv_inv] using mem_conjugate
  intro acting centralizes
  rw [Subgroup.mem_map_equiv]
  apply stronglyEmbedded_centralizer_le subgroup strong original original_mem
  rw [← involution_stabilizer_eq_centralizer, MulAction.mem_stabilizer_iff]
  have fixed : acting • involution = involution := by
    rw [← involution_stabilizer_eq_centralizer] at centralizes
    exact MulAction.mem_stabilizer_iff.mp centralizes
  change (conjugator⁻¹ * acting * conjugator) • (conjugator⁻¹ • involution) =
    conjugator⁻¹ • involution
  rw [smul_smul]
  have product_eq : (conjugator⁻¹ * acting * conjugator) * conjugator⁻¹ = conjugator⁻¹ * acting := by group
  rw [product_eq, mul_smul, fixed]

theorem unique_involutions_conjugate {group : Type*} [Group group]
    (subgroup : Subgroup group)
    (unique : ∀ first second : Involution group,
      first.val ∈ subgroup → second.val ∈ subgroup → first = second)
    (conjugator : group) (first second : Involution group)
    (first_mem : first.val ∈ subgroup.map (MulAut.conj conjugator).toMonoidHom)
    (second_mem : second.val ∈ subgroup.map (MulAut.conj conjugator).toMonoidHom) : first = second := by
  have equal : conjugator⁻¹ • first = conjugator⁻¹ • second := by
    apply unique
    · simpa only [involution_smul_val, MulAut.conj_symm_apply, inv_inv] using
        Subgroup.mem_map_equiv.mp first_mem
    · simpa only [involution_smul_val, MulAut.conj_symm_apply, inv_inv] using
        Subgroup.mem_map_equiv.mp second_mem
  have transported := congrArg (fun involution : Involution group => conjugator • involution) equal
  simpa only [smul_smul, mul_inv_cancel, one_smul] using transported

theorem core_free_pair_intersection {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (maximal : IsCoatom subgroup) (core_free : subgroup.normalCore = ⊥)
    (outside : Involution group) (outside_mem : outside.val ∉ subgroup) (conjugator : group)
    (mem_conjugate : outside.val ∈ subgroup.map (MulAut.conj conjugator).toMonoidHom) :
    subgroup ⊓ subgroup.map (MulAut.conj outside.val).toMonoidHom =
      subgroup ⊓ subgroup.map (MulAut.conj conjugator).toMonoidHom := by
  rw [core_free_pair_centralizer subgroup strong maximal core_free outside outside_mem]
  apply le_antisymm
  · exact inf_le_inf_left subgroup (conjugate_centralizer_le subgroup strong conjugator outside mem_conjugate)
  · intro acting acting_mem
    refine ⟨acting_mem.1, ?_⟩
    rw [← involution_stabilizer_eq_centralizer]
    apply MulAction.mem_stabilizer_iff.mpr
    apply unique_involutions_conjugate subgroup
      (core_free_involutions_unique subgroup strong maximal core_free) conjugator
    · exact CFSG.OrderReductions.OutsideInvolutions.conjugate_mem_of_mem _ acting outside acting_mem.2 mem_conjugate
    · exact mem_conjugate

theorem maximal_pair_intersection {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (maximal : IsCoatom subgroup) (outside : Involution group) (outside_mem : outside.val ∉ subgroup)
    (conjugator : group)
    (mem_conjugate : outside.val ∈ subgroup.map (MulAut.conj conjugator).toMonoidHom) :
    subgroup ⊓ subgroup.map (MulAut.conj outside.val).toMonoidHom =
      subgroup ⊓ subgroup.map (MulAut.conj conjugator).toMonoidHom := by
  let projection := QuotientGroup.mk' subgroup.normalCore
  let image := subgroup.map projection
  have odd_core := CFSG.OrderReductions.StrongEmbedding.normalCore_odd subgroup strong
  have odd_kernel : Odd (Nat.card projection.ker) := by
    rwa [QuotientGroup.ker_mk']
  let outside_image : Involution (group ⧸ subgroup.normalCore) :=
    ⟨projection outside.val, CFSG.OrderReductions.OddKernelInvolutions.involution_image_order
      projection odd_kernel outside⟩
  have kernel_le : projection.ker ≤ subgroup := by
    rw [QuotientGroup.ker_mk']
    exact subgroup.normalCore_le
  have image_outside : outside_image.val ∉ image := by
    intro mem_image
    have mem_preimage : outside.val ∈ image.comap projection := mem_image
    rw [Subgroup.comap_map_eq_self kernel_le] at mem_preimage
    exact outside_mem mem_preimage
  have image_mem : outside_image.val ∈ image.map (MulAut.conj (projection conjugator)).toMonoidHom := by
    have contains := Subgroup.mem_map_of_mem projection mem_conjugate
    rwa [CFSG.OrderReductions.StrongEmbeddingInheritance.map_conjugate] at contains
  have identity := core_free_pair_intersection image
    (CFSG.OrderReductions.StrongEmbeddingInheritance.surjective_odd_kernel_stronglyEmbedded projection
      (QuotientGroup.mk'_surjective _) subgroup strong kernel_le odd_kernel)
    (maximal_map_of_kernel_le projection (QuotientGroup.mk'_surjective _) subgroup maximal kernel_le)
    (quotient_core_free subgroup) outside_image image_outside (projection conjugator) image_mem
  apply Subgroup.map_injective_of_ker_le projection
  · apply le_inf kernel_le
    rw [QuotientGroup.ker_mk', Subgroup.normalCore_eq_iInf_map_conj]
    exact iInf_le _ outside.val
  · apply le_inf kernel_le
    rw [QuotientGroup.ker_mk', Subgroup.normalCore_eq_iInf_map_conj]
    exact iInf_le _ conjugator
  · rw [CFSG.OrderReductions.StrongEmbeddingInheritance.map_inf_of_ker_le projection _ _ kernel_le,
      CFSG.OrderReductions.StrongEmbeddingInheritance.map_inf_of_ker_le projection _ _ kernel_le,
      CFSG.OrderReductions.StrongEmbeddingInheritance.map_conjugate,
      CFSG.OrderReductions.StrongEmbeddingInheritance.map_conjugate]
    exact identity

end CFSG.OrderReductions.SolvableMaximal
