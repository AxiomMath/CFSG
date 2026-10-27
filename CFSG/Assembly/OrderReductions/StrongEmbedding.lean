module

public import Mathlib
public import CFSG.Mathlib.GroupTheory.Basic
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
public import CFSG.Open.OrderForm
public import CFSG.Assembly.OrderReductions.Helpers
public import CFSG.Assembly.OrderReductions.InvolutionGraph
public import CFSG.Assembly.OrderReductions.InvolutionFusion
public import CFSG.Assembly.OrderReductions.PermutationReduction
public import CFSG.Assembly.OrderReductions.UniqueInvolutionAction

public section

namespace CFSG.OrderReductions.StrongEmbedding

open CFSG.OrderReductions.InvolutionGraph

open scoped Pointwise

instance subgroupConjugationAction (group : Type*) [Group group] :
    MulAction group (Subgroup group) :=
  MulAction.compHom (Subgroup group) ConjAct.toConjAct.toMonoidHom

theorem subgroup_smul {group : Type*} [Group group]
    (conjugator : group) (subgroup : Subgroup group) :
    conjugator • subgroup = subgroup.map (MulAut.conj conjugator).toMonoidHom := rfl

abbrev Conjugates {group : Type*} [Group group] (subgroup : Subgroup group) :=
  MulAction.orbit group subgroup

theorem even_subgroup_normalizer_le {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (even_subgroup : Subgroup group) (contains : even_subgroup ≤ subgroup)
    (even_order : Even (Nat.card even_subgroup)) :
    Subgroup.normalizer (even_subgroup : Set group) ≤ subgroup := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 even_order.two_dvd
  let involution : Involution group :=
    ⟨element.val, by rw [Subgroup.orderOf_coe]; exact element_order⟩
  intro conjugator normalizes
  apply stronglyEmbedded_involution_conjugator_mem subgroup strong involution
    (contains element.property) conjugator
  apply contains
  exact (Subgroup.mem_normalizer_iff.mp normalizes involution.val).mp element.property

theorem normalizer_eq_self {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    Subgroup.normalizer (subgroup : Set group) = subgroup := by
  exact le_antisymm (even_subgroup_normalizer_le subgroup strong subgroup le_rfl strong.2.1)
    subgroup.le_normalizer

theorem sylow_inheritance {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (internal_sylow : Sylow 2 subgroup) :
    ∃ ambient_sylow : Sylow 2 group,
      (ambient_sylow : Subgroup group) =
        (internal_sylow : Subgroup subgroup).map subgroup.subtype := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  let image := (internal_sylow : Subgroup subgroup).map subgroup.subtype
  have image_two_group : IsPGroup 2 image := internal_sylow.isPGroup'.map subgroup.subtype
  have image_le : image ≤ subgroup := by
    intro element mem_image
    obtain ⟨preimage, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
    exact equal_image ▸ preimage.property
  have image_even : Even (Nat.card image) := by
    rw [show Nat.card image = Nat.card (internal_sylow : Subgroup subgroup) from
      Subgroup.card_map_of_injective Subtype.val_injective]
    exact even_iff_two_dvd.mpr (internal_sylow.dvd_card_of_dvd_card strong.2.1.two_dvd)
  obtain ⟨ambient_sylow, image_le_sylow⟩ := image_two_group.exists_le_sylow
  have normalizer_le : Subgroup.normalizer (image : Set group) ≤ subgroup :=
    even_subgroup_normalizer_le subgroup strong image image_le image_even
  let internal_normalizer :=
    (Subgroup.normalizer (image : Set group)).subgroupOf (ambient_sylow : Subgroup group)
  have internal_normalizer_two : IsPGroup 2 internal_normalizer :=
    ambient_sylow.isPGroup'.of_injective internal_normalizer.subtype Subtype.val_injective
  let ambient_normalizer :=
    Subgroup.normalizer (image : Set group) ⊓ (ambient_sylow : Subgroup group)
  have ambient_normalizer_le : ambient_normalizer ≤ subgroup :=
    inf_le_left.trans normalizer_le
  have ambient_normalizer_two : IsPGroup 2 (ambient_normalizer.subgroupOf subgroup) := by
    have image_normalizer_two := internal_normalizer_two.map
      (ambient_sylow : Subgroup group).subtype
    rw [Subgroup.subgroupOf_map_subtype] at image_normalizer_two
    have normalizer_two : IsPGroup 2
        ↥(Subgroup.normalizer (image : Set group) ⊓ (ambient_sylow : Subgroup group)) :=
      image_normalizer_two
    exact normalizer_two.of_equiv
      (Subgroup.subgroupOfEquivOfLe ambient_normalizer_le).symm
  refine ⟨ambient_sylow, ?_⟩
  have : Group.IsNilpotent (ambient_sylow : Subgroup group) :=
    ambient_sylow.isPGroup'.isNilpotent
  have normalizer_condition := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := (ambient_sylow : Subgroup group)))
  have image_full : image.subgroupOf (ambient_sylow : Subgroup group) = ⊤ := by
    apply normalizer_condition
    rw [← Subgroup.subgroupOf_normalizer_eq image_le_sylow]
    apply le_antisymm
    · intro element mem_normalizer
      have mem_subgroup : element.val ∈ subgroup :=
        normalizer_le (Subgroup.mem_subgroupOf.mp mem_normalizer)
      have mem_internal : (⟨element.val, mem_subgroup⟩ : subgroup) ∈
          ambient_normalizer.subgroupOf subgroup :=
        Subgroup.mem_subgroupOf.mpr
          ⟨Subgroup.mem_subgroupOf.mp mem_normalizer, element.property⟩
      have image_internal_le : (internal_sylow : Subgroup subgroup) ≤
          ambient_normalizer.subgroupOf subgroup := by
        intro internal_element mem_internal_sylow
        apply Subgroup.mem_subgroupOf.mpr
        have mem_image := Subgroup.mem_map_of_mem subgroup.subtype mem_internal_sylow
        exact ⟨image.le_normalizer mem_image, image_le_sylow mem_image⟩
      have maximal := internal_sylow.is_maximal' ambient_normalizer_two image_internal_le
      rw [maximal] at mem_internal
      apply Subgroup.mem_subgroupOf.mpr
      exact Subgroup.mem_map_of_mem subgroup.subtype mem_internal
    · exact Subgroup.subgroupOf_mono _ image.le_normalizer
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp image_full) image_le_sylow

theorem contains_sylow {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    ∃ sylow : Sylow 2 group, (sylow : Subgroup group) ≤ subgroup := by
  obtain ⟨internal_sylow⟩ := Sylow.nonempty (p := 2) (G := subgroup)
  obtain ⟨sylow, equal_image⟩ := sylow_inheritance subgroup strong internal_sylow
  refine ⟨sylow, ?_⟩
  rw [equal_image]
  intro element mem_image
  obtain ⟨preimage, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
  exact equal_image ▸ preimage.property

theorem odd_index {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) : Odd subgroup.index := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨sylow, contains⟩ := contains_sylow subgroup strong
  by_contra not_odd
  exact sylow.not_dvd_index
    ((Nat.not_odd_iff_even.mp not_odd).two_dvd.trans
      (Subgroup.index_dvd_of_le contains))

theorem involution_mem_conjugate {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (involution : Involution group) :
    ∃ conjugator : group,
      involution.val ∈ subgroup.map (MulAut.conj conjugator).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨first_sylow, contains⟩ := contains_sylow subgroup strong
  obtain ⟨second_sylow, mem_second⟩ := exists_sylow_containing_involution involution
  obtain ⟨conjugator, conjugates⟩ :=
    MulAction.exists_smul_eq group first_sylow second_sylow
  refine ⟨conjugator, ?_⟩
  change involution.val ∈ (second_sylow : Set group) at mem_second
  rw [← conjugates, Sylow.coe_smul] at mem_second
  obtain ⟨preimage, mem_first, equal_image⟩ := mem_second
  exact Subgroup.mem_map.mpr ⟨preimage, contains mem_first, equal_image⟩

theorem normalCore_odd {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    Odd (Nat.card subgroup.normalCore) := by
  classical
  have outside : ∃ conjugator : group, conjugator ∉ subgroup := by
    by_contra no_outside
    push Not at no_outside
    exact strong.1 (subgroup.eq_top_iff'.mpr no_outside)
  obtain ⟨conjugator, not_mem⟩ := outside
  have core_le : subgroup.normalCore ≤
      subgroup ⊓ subgroup.map (MulAut.conj conjugator).toMonoidHom := by
    apply le_inf subgroup.normalCore_le
    rw [Subgroup.normalCore_eq_iInf_map_conj]
    exact iInf_le _ conjugator
  have card_divides := Subgroup.card_dvd_of_le core_le
  by_contra not_odd
  exact (strong.2.2 conjugator not_mem).not_two_dvd_nat
    ((Nat.not_odd_iff_even.mp not_odd).two_dvd.trans card_divides)

theorem coset_card_odd {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    Odd (Nat.card (group ⧸ subgroup)) := by
  rw [← subgroup.index_eq_card]
  exact odd_index subgroup strong

theorem coset_card_ge_three {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    3 ≤ Nat.card (group ⧸ subgroup) := by
  have odd_card := coset_card_odd subgroup strong
  have positive : 0 < Nat.card (group ⧸ subgroup) := Nat.card_pos
  have not_one : Nat.card (group ⧸ subgroup) ≠ 1 := by
    rw [← subgroup.index_eq_card]
    exact fun equal_one => strong.1 (Subgroup.index_eq_one.mp equal_one)
  obtain ⟨half, card_eq⟩ := odd_card
  omega

theorem involution_fixed_coset_iff {group : Type*} [Group group]
    (subgroup : Subgroup group) (involution : Involution group) (representative : group) :
    involution.val • (representative : group ⧸ subgroup) = representative ↔
      (representative⁻¹ • involution).val ∈ subgroup := by
  change ((involution.val * representative : group) : group ⧸ subgroup) = representative ↔ _
  rw [QuotientGroup.eq, involution_smul_val]
  simp only [mul_inv_rev, inv_eq_self_of_orderOf_eq_two involution.property, mul_assoc, inv_inv]

theorem involution_unique_fixed_coset {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (involution : Involution group) :
    ∃! coset : group ⧸ subgroup, involution.val • coset = coset := by
  obtain ⟨representative, mem_conjugate⟩ := involution_mem_conjugate subgroup strong involution
  have mem_internal : (representative⁻¹ • involution).val ∈ subgroup := by
    rw [Subgroup.mem_map_equiv] at mem_conjugate
    simpa only [involution_smul_val, MulAut.conj_symm_apply, inv_inv] using mem_conjugate
  refine ⟨(representative : group ⧸ subgroup),
    (involution_fixed_coset_iff subgroup involution representative).mpr mem_internal, ?_⟩
  intro other
  induction other using QuotientGroup.induction_on with
  | H other =>
      intro fixed
      have other_mem := (involution_fixed_coset_iff subgroup involution other).mp fixed
      have conjugates_mem :
          ((other⁻¹ * representative) • (representative⁻¹ • involution)).val ∈ subgroup := by
        rw [smul_smul, mul_assoc, mul_inv_cancel, mul_one]
        exact other_mem
      have conjugator_mem := stronglyEmbedded_involution_conjugator_mem subgroup strong
        (representative⁻¹ • involution) mem_internal (other⁻¹ * representative) conjugates_mem
      exact QuotientGroup.eq.mpr conjugator_mem

theorem simple_coset_action_injective {group : Type*} [Group group] [IsSimpleGroup group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    Function.Injective (MulAction.toPermHom group (group ⧸ subgroup)) :=
  CFSG.OrderReductions.PermutationReduction.simple_coset_action_injective group subgroup strong.1

theorem subgroup_stabilizer_eq {group : Type*} [Group group]
    (subgroup : Subgroup group) :
    MulAction.stabilizer group subgroup = Subgroup.normalizer (subgroup : Set group) := by
  ext element
  rw [MulAction.mem_stabilizer_iff, subgroup_smul, Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

theorem stronglyEmbedded_stabilizer_eq {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    MulAction.stabilizer group subgroup = subgroup := by
  rw [subgroup_stabilizer_eq, normalizer_eq_self subgroup strong]

theorem conjugate_stabilizer_eq {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (conjugate : Conjugates subgroup) :
    MulAction.stabilizer group conjugate = conjugate.val := by
  have ambient_eq : MulAction.stabilizer group conjugate.val = conjugate.val := by
    obtain ⟨conjugator, conjugates⟩ := conjugate.property
    change conjugator • subgroup = conjugate.val at conjugates
    rw [← conjugates, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      stronglyEmbedded_stabilizer_eq subgroup strong, subgroup_smul]
  ext element
  rw [MulAction.mem_stabilizer_iff, ← ambient_eq, MulAction.mem_stabilizer_iff]
  exact Subtype.ext_iff

@[expose] noncomputable def cosetEquivConjugates {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    (group ⧸ subgroup) ≃ Conjugates subgroup :=
  (Equiv.cast (congrArg (fun stabilizer : Subgroup group => group ⧸ stabilizer)
    (stronglyEmbedded_stabilizer_eq subgroup strong).symm)).trans
      (MulAction.orbitEquivQuotientStabilizer group subgroup).symm

theorem conjugates_card_odd {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    Odd (Nat.card (Conjugates subgroup)) := by
  rw [← Nat.card_congr (cosetEquivConjugates subgroup strong)]
  exact coset_card_odd subgroup strong

theorem conjugates_card_ge_three {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    3 ≤ Nat.card (Conjugates subgroup) := by
  rw [← Nat.card_congr (cosetEquivConjugates subgroup strong)]
  exact coset_card_ge_three subgroup strong

theorem involution_mem_conjugate_unique {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (involution : Involution group) :
    ∃! conjugate : Conjugates subgroup, involution.val ∈ conjugate.val := by
  obtain ⟨representative, mem_conjugate⟩ := involution_mem_conjugate subgroup strong involution
  refine ⟨⟨representative • subgroup, ⟨representative, rfl⟩⟩, mem_conjugate, ?_⟩
  intro other other_mem
  obtain ⟨other_representative, other_eq⟩ := other.property
  change other_representative • subgroup = other.val at other_eq
  have mem_internal : (representative⁻¹ • involution).val ∈ subgroup := by
    rw [Subgroup.mem_map_equiv] at mem_conjugate
    simpa only [involution_smul_val, MulAut.conj_symm_apply, inv_inv] using mem_conjugate
  have other_internal : (other_representative⁻¹ • involution).val ∈ subgroup := by
    rw [← other_eq, subgroup_smul, Subgroup.mem_map_equiv] at other_mem
    simpa only [involution_smul_val, MulAut.conj_symm_apply, inv_inv] using other_mem
  have conjugates_mem :
      ((other_representative⁻¹ * representative) • (representative⁻¹ • involution)).val ∈
        subgroup := by
    rw [smul_smul, mul_assoc, mul_inv_cancel, mul_one]
    exact other_internal
  have conjugator_mem := stronglyEmbedded_involution_conjugator_mem subgroup strong
    (representative⁻¹ • involution) mem_internal
    (other_representative⁻¹ * representative) conjugates_mem
  have fixed_subgroup : (other_representative⁻¹ * representative) • subgroup = subgroup :=
    MulAction.mem_stabilizer_iff.mp
      ((stronglyEmbedded_stabilizer_eq subgroup strong).symm ▸ conjugator_mem)
  apply Subtype.ext
  change other.val = representative • subgroup
  rw [← other_eq]
  apply (MulAction.injective other_representative⁻¹)
  change other_representative⁻¹ • other_representative • subgroup =
    other_representative⁻¹ • representative • subgroup
  rw [inv_smul_smul, ← mul_smul, fixed_subgroup]

theorem involution_unique_fixed_conjugate {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (involution : Involution group) :
    ∃! conjugate : Conjugates subgroup, involution.val • conjugate = conjugate := by
  obtain ⟨conjugate, mem_conjugate, unique⟩ :=
    involution_mem_conjugate_unique subgroup strong involution
  have fixed_iff (candidate : Conjugates subgroup) :
      involution.val • candidate = candidate ↔ involution.val ∈ candidate.val := by
    rw [← conjugate_stabilizer_eq subgroup strong candidate, MulAction.mem_stabilizer_iff]
  exact ⟨conjugate, (fixed_iff conjugate).mpr mem_conjugate,
    fun candidate fixed => unique candidate ((fixed_iff candidate).mp fixed)⟩

theorem simple_conjugate_action_injective {group : Type*} [Group group] [Finite group]
    [IsSimpleGroup group] (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    Function.Injective (MulAction.toPermHom group (Conjugates subgroup)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases CFSG.eq_bot_or_eq_top_of_normal
    (MulAction.toPermHom group (Conjugates subgroup)).ker inferInstance with
    kernel_bot | kernel_top
  · exact kernel_bot
  · exfalso
    apply strong.1
    apply subgroup.eq_top_iff'.mpr
    intro element
    let base : Conjugates subgroup := ⟨subgroup, ⟨1, one_smul group subgroup⟩⟩
    have mem_kernel : element ∈ (MulAction.toPermHom group (Conjugates subgroup)).ker := by
      rw [kernel_top]
      trivial
    have fixes_base : element • base = base := by
      exact congrArg (fun permutation : Equiv.Perm (Conjugates subgroup) => permutation base)
        mem_kernel
    change element ∈ base.val
    rw [← conjugate_stabilizer_eq subgroup strong base, MulAction.mem_stabilizer_iff]
    exact fixes_base

theorem involutions_conjugate_in_subgroup {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (first second : Involution group) (first_mem : first.val ∈ subgroup)
    (second_mem : second.val ∈ subgroup) :
    ∃ conjugator : subgroup, conjugator.val • first = second := by
  obtain ⟨conjugator, conjugates⟩ :=
    CFSG.OrderReductions.InvolutionFusion.all_involutions_conjugate_of_disconnected
      (stronglyEmbedded_not_preconnected subgroup strong) first second
  have mem_subgroup := stronglyEmbedded_involution_conjugator_mem subgroup strong first first_mem
    conjugator (conjugates ▸ second_mem)
  exact ⟨⟨conjugator, mem_subgroup⟩, conjugates⟩

theorem involutions_transitive {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    MulAction.IsPretransitive subgroup (Involution subgroup) := by
  constructor
  intro first second
  let first_ambient := mapInvolution subgroup.subtype Subtype.val_injective first
  let second_ambient := mapInvolution subgroup.subtype Subtype.val_injective second
  obtain ⟨conjugator, conjugates⟩ := involutions_conjugate_in_subgroup subgroup strong
    first_ambient second_ambient first.val.property second.val.property
  refine ⟨conjugator, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have ambient_eq := congrArg Subtype.val conjugates
  exact ambient_eq

theorem two_subgroup_free_on_other_conjugates {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (two_subgroup : Subgroup group) (two_group : IsPGroup 2 two_subgroup)
    (contains : two_subgroup ≤ subgroup) (element : two_subgroup)
    (conjugate : Conjugates subgroup) (other : conjugate.val ≠ subgroup)
    (fixed : element.val • conjugate = conjugate) : element = 1 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_contra nontrivial
  obtain ⟨conjugator, conjugates⟩ := conjugate.property
  change conjugator • subgroup = conjugate.val at conjugates
  have not_mem : conjugator ∉ subgroup := by
    intro mem_subgroup
    have fixes_subgroup : conjugator • subgroup = subgroup :=
      MulAction.mem_stabilizer_iff.mp
        ((stronglyEmbedded_stabilizer_eq subgroup strong).symm ▸ mem_subgroup)
    exact other (conjugates.symm.trans fixes_subgroup)
  have mem_conjugate : element.val ∈ conjugate.val := by
    rw [← conjugate_stabilizer_eq subgroup strong conjugate, MulAction.mem_stabilizer_iff]
    exact fixed
  have mem_intersection : element.val ∈
      subgroup ⊓ subgroup.map (MulAut.conj conjugator).toMonoidHom := by
    refine ⟨contains element.property, ?_⟩
    rw [← subgroup_smul, conjugates]
    exact mem_conjugate
  have two_divides_order : 2 ∣ orderOf element.val := by
    rw [Subgroup.orderOf_coe]
    exact two_group.dvd_orderOf nontrivial
  exact (strong.2.2 conjugator not_mem).not_two_dvd_nat
    (two_divides_order.trans (Subgroup.orderOf_dvd_natCard _ mem_intersection))

@[expose] def otherConjugates {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (two_subgroup : Subgroup group) (contains : two_subgroup ≤ subgroup) :
    SubMulAction two_subgroup (Conjugates subgroup) where
  carrier := {conjugate | conjugate.val ≠ subgroup}
  smul_mem' := by
    intro element conjugate other equal_subgroup
    have fixes_subgroup : element.val • subgroup = subgroup :=
      MulAction.mem_stabilizer_iff.mp
        ((stronglyEmbedded_stabilizer_eq subgroup strong).symm ▸ contains element.property)
    apply other
    apply (MulAction.injective element.val)
    change element.val • conjugate.val = element.val • subgroup
    exact equal_subgroup.trans fixes_subgroup.symm

theorem two_subgroup_card_dvd_other_conjugates {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (two_subgroup : Subgroup group) (two_group : IsPGroup 2 two_subgroup)
    (contains : two_subgroup ≤ subgroup) :
    Nat.card two_subgroup ∣ Nat.card (Conjugates subgroup) - 1 := by
  classical
  let complement := otherConjugates subgroup strong two_subgroup contains
  let _ : Fintype two_subgroup := Fintype.ofFinite two_subgroup
  let _ : Fintype complement := Fintype.ofFinite complement
  have stabilizer_bot (conjugate : complement) :
      MulAction.stabilizer two_subgroup conjugate = ⊥ := by
    apply eq_bot_iff.mpr
    intro element stabilizes
    change element = 1
    apply two_subgroup_free_on_other_conjugates subgroup strong two_subgroup two_group contains
      element conjugate.val conjugate.property
    exact congrArg Subtype.val stabilizes
  have divides : Nat.card two_subgroup ∣ Nat.card complement := by
    let _ : Fintype (Quotient (MulAction.orbitRel two_subgroup complement)) := Fintype.ofFinite _
    let _ (conjugate : complement) : Fintype (MulAction.stabilizer two_subgroup conjugate) :=
      Fintype.ofFinite _
    have card_sum := MulAction.card_eq_sum_card_group_div_card_stabilizer two_subgroup complement
    have stabilizer_card (conjugate : complement) :
        Fintype.card (MulAction.stabilizer two_subgroup conjugate) = 1 := by
      rw [← Nat.card_eq_fintype_card, stabilizer_bot, Subgroup.card_bot]
    simp only [stabilizer_card, Nat.div_one, Finset.sum_const, smul_eq_mul] at card_sum
    simp only [Nat.card_eq_fintype_card]
    rw [card_sum]
    exact dvd_mul_left _ _
  have complement_card : Nat.card complement = Nat.card (Conjugates subgroup) - 1 := by
    change Nat.card {conjugate : Conjugates subgroup // conjugate.val ≠ subgroup} = _
    let base : Conjugates subgroup := ⟨subgroup, ⟨1, one_smul group subgroup⟩⟩
    have predicates : (fun conjugate : Conjugates subgroup => conjugate.val ≠ subgroup) =
        (fun conjugate => conjugate ∈ ({base} : Set (Conjugates subgroup))ᶜ) := by
      funext conjugate
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff]
      rfl
    rw [predicates, ← Set.ncard_univ, Set.ncard_coe, Set.ncard_compl, Set.ncard_singleton]
  rwa [complement_card] at divides

theorem sylow_card_dvd_index_sub_one {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) (sylow : Sylow 2 group)
    (contains : (sylow : Subgroup group) ≤ subgroup) :
    Nat.card (sylow : Subgroup group) ∣ subgroup.index - 1 := by
  have divides := two_subgroup_card_dvd_other_conjugates subgroup strong
    (sylow : Subgroup group) sylow.isPGroup' contains
  rw [← Nat.card_congr (cosetEquivConjugates subgroup strong), ← subgroup.index_eq_card] at divides
  exact divides

theorem sylow_card_lt_index {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) (sylow : Sylow 2 group)
    (contains : (sylow : Subgroup group) ≤ subgroup) :
    Nat.card (sylow : Subgroup group) < subgroup.index := by
  have index_bound := coset_card_ge_three subgroup strong
  rw [← subgroup.index_eq_card] at index_bound
  have card_bound := Nat.le_of_dvd (by omega : 0 < subgroup.index - 1)
    (sylow_card_dvd_index_sub_one subgroup strong sylow contains)
  omega

theorem perfect_index_mod_four {group : Type*} [Group group] [Finite group]
    [Group.IsPerfect group] (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    subgroup.index % 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 strong.2.1.two_dvd
  let involution : Involution group :=
    ⟨element.val, by rw [Subgroup.orderOf_coe]; exact element_order⟩
  rw [subgroup.index_eq_card]
  exact CFSG.OrderReductions.UniqueInvolutionAction.perfect_unique_involution_action_card_mod_four
    involution (involution_unique_fixed_coset subgroup strong involution)

theorem perfect_component_card_mod_four {group : Type*} [Group group] [Finite group]
    [Group.IsPerfect group] (component : Component group) :
    Nat.card (Component group) % 4 = 1 := by
  induction component using SimpleGraph.ConnectedComponent.ind with
  | h involution =>
      exact CFSG.OrderReductions.UniqueInvolutionAction.perfect_unique_involution_action_card_mod_four
        involution (involution_unique_fixed_component involution)

theorem simple_card_mem_orders_of_stronglyEmbedded_index_le_eight {group : Type*} [Group group]
    [Finite group] [IsSimpleGroup group] (subgroup : Subgroup group)
    (strong : StronglyEmbedded subgroup) (small : subgroup.index ≤ 8) :
    Nat.card group ∈ CFSG.Open.cfsgOrders := by
  classical
  by_cases commutative : IsMulCommutative group
  · let := commutative
    exact CFSG.OrderReductions.Helpers.card_mem_cfsgOrders_of_simple_commutative group
  · have : Group.IsPerfect group := CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect
      group commutative
    have congruence := perfect_index_mod_four subgroup strong
    exact CFSG.OrderReductions.PermutationReduction.simple_card_mem_orders_of_index_le_six
      group subgroup strong.1 (by omega)

theorem involution_card_eq_index_mul {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    Nat.card (Involution group) = subgroup.index * Nat.card (Involution subgroup) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 strong.2.1.two_dvd
  let internal_involution : Involution subgroup := ⟨element, element_order⟩
  let ambient_involution := mapInvolution subgroup.subtype Subtype.val_injective internal_involution
  have ambient_transitive : MulAction.IsPretransitive group (Involution group) :=
    ⟨CFSG.OrderReductions.InvolutionFusion.all_involutions_conjugate_of_disconnected
      (stronglyEmbedded_not_preconnected subgroup strong)⟩
  have internal_transitive := involutions_transitive subgroup strong
  have ambient_product := CFSG.OrderReductions.InvolutionFusion.involution_card_mul_centralizer_card
    ambient_transitive ambient_involution
  have internal_product := CFSG.OrderReductions.InvolutionFusion.involution_card_mul_centralizer_card
    internal_transitive internal_involution
  have center_le : Subgroup.centralizer ({ambient_involution.val} : Set group) ≤ subgroup :=
    stronglyEmbedded_centralizer_le subgroup strong ambient_involution element.property
  have center_subgroupOf :
      (Subgroup.centralizer ({ambient_involution.val} : Set group)).subgroupOf subgroup =
        Subgroup.centralizer ({internal_involution.val} : Set subgroup) := by
    ext element
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro centralizes other other_mem
      have other_eq : other = internal_involution.val := by simpa using other_mem
      rw [other_eq]
      apply Subtype.ext
      exact centralizes ambient_involution.val (by simp)
    · intro centralizes other other_mem
      have other_eq : other = ambient_involution.val := by simpa using other_mem
      rw [other_eq]
      exact congrArg Subtype.val (centralizes internal_involution.val (by simp))
  have equal_centers :
      Nat.card (Subgroup.centralizer ({internal_involution.val} : Set subgroup)) =
        Nat.card (Subgroup.centralizer ({ambient_involution.val} : Set group)) := by
    rw [← center_subgroupOf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe center_le).toEquiv
  rw [equal_centers] at internal_product
  have card_index := subgroup.card_mul_index
  have positive : 0 < Nat.card (Subgroup.centralizer ({ambient_involution.val} : Set group)) :=
    Nat.card_pos
  nlinarith

end CFSG.OrderReductions.StrongEmbedding
