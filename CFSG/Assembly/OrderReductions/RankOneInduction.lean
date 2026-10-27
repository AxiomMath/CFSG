module

public import CFSG.Assembly.OrderReductions.OddKernelInvolutions
public import CFSG.Assembly.OrderReductions.Reduction
public import CFSG.Assembly.OrderReductions.CyclicTwoTransfer

public section

namespace CFSG.OrderReductions.RankOneInduction

universe group_universe

open CFSG.OrderReductions.InvolutionGraph

@[expose] def NoFourInvolutions (group : Type*) [Group group] : Prop :=
  ∀ first second : Involution group, Commute first.val second.val → first = second

theorem noFourInvolutions_subgroup {group : Type*} [Group group]
    (no_four : NoFourInvolutions group) (subgroup : Subgroup group) : NoFourInvolutions subgroup := by
  intro first second commutes
  have equal_images := no_four (mapInvolution subgroup.subtype Subtype.val_injective first)
    (mapInvolution subgroup.subtype Subtype.val_injective second) (commutes.map subgroup.subtype)
  have equal_values : first.val.val = second.val.val :=
    congrArg (fun current : Involution group => current.val) equal_images
  exact Subtype.ext (Subtype.ext equal_values)

theorem noFourInvolutions_quotient {group : Type*} [Group group] [Finite group]
    (no_four : NoFourInvolutions group) (normal : Subgroup group) [normal.Normal]
    (odd_normal : Odd (Nat.card normal)) : NoFourInvolutions (group ⧸ normal) := by
  apply CFSG.OrderReductions.OddKernelInvolutions.quotient_no_four_involutions
    (QuotientGroup.mk' normal) (QuotientGroup.mk'_surjective normal) _ no_four
  rw [QuotientGroup.ker_mk']
  exact odd_normal

theorem involution_central_of_normal_centrality {group : Type*} [Group group]
    (no_four : NoFourInvolutions group) (normal : Subgroup group) [normal.Normal]
    (involution : Involution group) (mem_normal : involution.val ∈ normal)
    (central : (⟨involution.val, mem_normal⟩ : normal) ∈ Subgroup.center normal) :
    involution.val ∈ Subgroup.center group := by
  apply Subgroup.mem_center_iff.mpr
  intro element
  have conjugate_mem : (element • involution).val ∈ normal :=
    (inferInstance : normal.Normal).conj_mem involution.val mem_normal element
  have commute_values : Commute involution.val (element • involution).val := by
    have internal_commutes :=
      (Subgroup.mem_center_iff.mp central) ⟨(element • involution).val, conjugate_mem⟩
    exact (congrArg Subtype.val internal_commutes).symm
  have equal_conjugate := no_four involution (element • involution) commute_values
  have fixed : element * involution.val * element⁻¹ = involution.val :=
    (congrArg Subtype.val equal_conjugate).symm
  exact mul_inv_eq_iff_eq_mul.mp fixed

theorem coreFree_centrality_of_proper_normal_step
    (proper_normal_step : ∀ (group : Type group_universe) [Group group] [Finite group],
      NoFourInvolutions group → CFSG.OrderReductions.OddCore.oddCore group = ⊥ →
      ∀ involution : Involution group,
        (∃ normal : Subgroup group, normal.Normal ∧ normal ≠ ⊤ ∧ involution.val ∈ normal) ∨
        ∃ sylow : Sylow 2 group, IsCyclic sylow)
    (group : Type group_universe) [Group group] [Finite group]
    (no_four : NoFourInvolutions group) (core_bot : CFSG.OrderReductions.OddCore.oddCore group = ⊥)
    (involution : Involution group) : involution.val ∈ Subgroup.center group := by
  classical
  generalize order_eq : Nat.card group = order
  induction order using Nat.strong_induction_on generalizing group with
  | h order induction_hypothesis =>
      rcases proper_normal_step group no_four core_bot involution with
        ⟨normal, normal_normal, normal_proper, mem_normal⟩ | ⟨sylow, cyclic⟩
      · have := normal_normal
        let internal : Involution normal :=
          ⟨⟨involution.val, mem_normal⟩, by rw [← Subgroup.orderOf_coe]; exact involution.property⟩
        have smaller : Nat.card normal < order := by
          rw [← order_eq]
          exact CFSG.OrderReductions.Reduction.proper_subgroup_card_lt group normal normal_proper
        have internal_central := induction_hypothesis (Nat.card normal) smaller normal
          (noFourInvolutions_subgroup no_four normal)
          (CFSG.OrderReductions.OddCore.normal_subgroup_oddCore_eq_bot core_bot normal) internal rfl
        exact involution_central_of_normal_centrality no_four normal involution mem_normal internal_central
      · have even_group : Even (Nat.card group) := by
          have divides := orderOf_dvd_natCard involution.val
          rw [involution.property] at divides
          exact even_iff_two_dvd.mpr divides
        exact CFSG.OrderReductions.CyclicTwoTransfer.involution_central_of_cyclic_sylow_and_oddCore_bot
          even_group core_bot sylow cyclic involution

theorem involution_image_central_of_coreFree_centrality
    (centrality : ∀ (group : Type group_universe) [Group group] [Finite group],
      NoFourInvolutions group → CFSG.OrderReductions.OddCore.oddCore group = ⊥ →
      ∀ involution : Involution group, involution.val ∈ Subgroup.center group)
    (group : Type group_universe) [Group group] [Finite group] (no_four : NoFourInvolutions group)
    (involution : Involution group) :
    QuotientGroup.mk' (CFSG.OrderReductions.OddCore.oddCore group) involution.val ∈
      Subgroup.center (group ⧸ CFSG.OrderReductions.OddCore.oddCore group) := by
  let projection := QuotientGroup.mk' (CFSG.OrderReductions.OddCore.oddCore group)
  have kernel_odd : Odd (Nat.card projection.ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.OrderReductions.OddCore.oddCore_odd group
  let image : Involution (group ⧸ CFSG.OrderReductions.OddCore.oddCore group) :=
    ⟨projection involution.val,
      CFSG.OrderReductions.OddKernelInvolutions.involution_image_order projection kernel_odd involution⟩
  exact centrality _
    (noFourInvolutions_quotient no_four _ (CFSG.OrderReductions.OddCore.oddCore_odd group))
    (CFSG.OrderReductions.OddCore.oddCore_quotient_eq_bot group) image

end CFSG.OrderReductions.RankOneInduction
