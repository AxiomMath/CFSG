module

public import CFSG.Assembly.OrderReductions.ThompsonCenter
public import CFSG.Assembly.OrderReductions.ActionPrimeCore

public section

namespace CFSG.OrderReductions.ThompsonFixedGrowth

open CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.ThompsonCenter

@[expose] def fixedPreimage {group : Type*} [Group group]
    (subgroup kernel : Subgroup group) [kernel.Normal] : Subgroup group :=
  subgroup ⊓ (Subgroup.center (group ⧸ kernel)).comap (QuotientGroup.mk' kernel)

instance fixedPreimage_normal {group : Type*} [Group group]
    (subgroup kernel : Subgroup group) [subgroup.Normal] [kernel.Normal] :
    (fixedPreimage subgroup kernel).Normal :=
  inferInstanceAs (subgroup ⊓ (Subgroup.center (group ⧸ kernel)).comap (QuotientGroup.mk' kernel)).Normal

theorem fixedPreimage_le {group : Type*} [Group group]
    (subgroup kernel : Subgroup group) [kernel.Normal] : fixedPreimage subgroup kernel ≤ subgroup := inf_le_left

theorem kernel_le_fixedPreimage {group : Type*} [Group group]
    (subgroup kernel : Subgroup group) [kernel.Normal] (contains : kernel ≤ subgroup) :
    kernel ≤ fixedPreimage subgroup kernel :=
  le_inf contains (QuotientGroup.le_comap_mk' kernel _)

theorem normal_prime_subgroup_has_central_element {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group)
    (normal : Subgroup group) [normal.Normal] (nontrivial : normal ≠ ⊥) :
    ∃ element : group, element ∈ normal ∧ element ∈ Subgroup.center group ∧ element ≠ 1 := by
  have normal_nontrivial : Nontrivial normal := (Subgroup.nontrivial_iff_ne_bot normal).mpr nontrivial
  have prime_normal := prime_group.to_subgroup normal
  have divides : prime ∣ Nat.card normal := by
    rcases prime_normal.card_eq_or_dvd with card_one | divides
    · exact False.elim (nontrivial (Subgroup.card_eq_one.mp card_one))
    · exact divides
  let action := conjugationAction normal
  let := MulDistribMulAction.compHom normal action
  have fixed_one : (1 : normal) ∈ MulAction.fixedPoints group normal := by
    apply MulAction.mem_fixedPoints.mpr
    intro actor
    change action actor 1 = 1
    exact map_one (action actor)
  obtain ⟨element, fixed, distinct⟩ :=
    prime_group.exists_fixed_point_of_prime_dvd_card_of_fixed_point normal divides fixed_one
  refine ⟨element.val, element.property, Subgroup.mem_center_iff.mpr ?_, ?_⟩
  · intro actor
    have equal := congrArg (fun value : normal => value.val) (MulAction.mem_fixedPoints.mp fixed actor)
    change (conjugationAction normal actor element).val = element.val at equal
    rw [conjugationAction_apply] at equal
    have multiplied := congrArg (fun value : group => value * actor) equal
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using multiplied
  · intro equal
    exact distinct (Subtype.ext equal.symm)

theorem kernel_lt_fixedPreimage {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group)
    (subgroup kernel : Subgroup group) [subgroup.Normal] [kernel.Normal] (proper : kernel < subgroup) :
    kernel < fixedPreimage subgroup kernel := by
  let projection := QuotientGroup.mk' kernel
  have image_nontrivial : subgroup.map projection ≠ ⊥ := by
    intro image_bot
    have subgroup_le := (Subgroup.map_eq_bot_iff subgroup).mp image_bot
    rw [QuotientGroup.ker_mk'] at subgroup_le
    exact not_le_of_gt proper subgroup_le
  obtain ⟨element, element_mem, central, nonidentity⟩ := normal_prime_subgroup_has_central_element
    prime (prime_group.to_quotient kernel) (subgroup.map projection) image_nontrivial
  obtain ⟨original, original_mem, image_eq⟩ := Subgroup.mem_map.mp element_mem
  have original_fixed : original ∈ fixedPreimage subgroup kernel := by
    refine ⟨original_mem, ?_⟩
    change projection original ∈ Subgroup.center (group ⧸ kernel)
    rwa [image_eq]
  apply lt_of_le_of_ne (kernel_le_fixedPreimage subgroup kernel proper.le)
  intro equal
  have original_kernel : original ∈ projection.ker := by
    rw [QuotientGroup.ker_mk', equal]
    exact original_fixed
  exact nonidentity (image_eq.symm.trans (MonoidHom.mem_ker.mp original_kernel))

theorem fixedPreimage_commutator_le_kernel {group : Type*} [Group group]
    (subgroup kernel : Subgroup group) [kernel.Normal] :
    ⁅fixedPreimage subgroup kernel, ⊤⁆ ≤ kernel := by
  let projection := QuotientGroup.mk' kernel
  have image_le : (fixedPreimage subgroup kernel).map projection ≤ Subgroup.center (group ⧸ kernel) :=
    Subgroup.map_le_iff_le_comap.mpr inf_le_right
  have commutator_le := Subgroup.commutator_mono image_le (show (⊤ : Subgroup group).map projection ≤ ⊤ from le_top)
  rw [← Subgroup.map_commutator, Subgroup.commutator_center_left] at commutator_le
  have image_bot := le_bot_iff.mp commutator_le
  have kernel_le := (Subgroup.map_eq_bot_iff _).mp image_bot
  rwa [QuotientGroup.ker_mk'] at kernel_le

theorem thompson_fixed_growth {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group)
    (kernel : Subgroup group) [kernel.Normal] (proper : kernel < thompsonCenter group) :
    kernel < fixedPreimage (thompsonCenter group) kernel ∧
      fixedPreimage (thompsonCenter group) kernel ≤ thompsonCenter group ∧
        IsMulCommutative ↥(fixedPreimage (thompsonCenter group) kernel) ∧
          ⁅fixedPreimage (thompsonCenter group) kernel, ⊤⁆ ≤ kernel := by
  have : IsMulCommutative (thompsonCenter group) := by
    change IsMulCommutative ((Subgroup.center (thompson group)).map (thompson group).subtype)
    infer_instance
  refine ⟨kernel_lt_fixedPreimage prime prime_group _ kernel proper, inf_le_left, ?_,
    fixedPreimage_commutator_le_kernel _ kernel⟩
  exact IsMulCommutative.of_setLike_mul_comm
    (fun _ first_mem _ second_mem => setLike_mul_comm (s := thompsonCenter group) first_mem.1 second_mem.1)

end CFSG.OrderReductions.ThompsonFixedGrowth
