module

public import CFSG.Assembly.OrderReductions.ActionPrimeCore
public import CFSG.Assembly.OrderReductions.ReplacementGeometry

public section

namespace CFSG.OrderReductions.PrimeQuotientFrattini

open scoped Pointwise

theorem kernel_sup_sylow_eq_top {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (kernel : Subgroup group) [kernel.Normal]
    (prime_quotient : IsPGroup prime (group ⧸ kernel)) (sylow : Sylow prime group) :
    kernel ⊔ (sylow : Subgroup group) = ⊤ := by
  let projection := QuotientGroup.mk' kernel
  let image := sylow.mapSurjective (QuotientGroup.mk'_surjective kernel)
  have image_top : (image : Subgroup (group ⧸ kernel)) = ⊤ :=
    (image.is_maximal' (prime_quotient.to_subgroup ⊤) le_top).symm
  have map_eq : (sylow : Subgroup group).map projection = (⊤ : Subgroup group).map projection := by
    rw [Subgroup.map_top_of_surjective projection (QuotientGroup.mk'_surjective kernel)]
    exact (Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective kernel) sylow).symm.trans image_top
  have equal := Subgroup.map_eq_map_iff.mp map_eq
  rwa [QuotientGroup.ker_mk', top_sup_eq, sup_comm] at equal

theorem normal_prime_quotient_frattini {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (kernel normal : Subgroup group) [kernel.Normal] [normal.Normal]
    (contains : kernel ≤ normal) (prime_quotient : IsPGroup prime (normal ⧸ kernel.subgroupOf normal))
    (sylow : Sylow prime normal) :
    kernel ⊔ (sylow : Subgroup normal).map normal.subtype = normal ∧
      kernel ⊔ Subgroup.normalizer (((sylow : Subgroup normal).map normal.subtype) : Set group) = ⊤ := by
  let image := (sylow : Subgroup normal).map normal.subtype
  have internal_top := kernel_sup_sylow_eq_top prime (kernel.subgroupOf normal) prime_quotient sylow
  have product_eq := congrArg (Subgroup.map normal.subtype) internal_top
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le contains,
    ← MonoidHom.range_eq_map, Subgroup.subtype_range] at product_eq
  refine ⟨product_eq, ?_⟩
  have frattini := sylow.normalizer_sup_eq_top
  change Subgroup.normalizer (image : Set group) ⊔ normal = ⊤ at frattini
  change kernel ⊔ image = normal at product_eq
  rw [← product_eq, ← sup_assoc, sup_comm (Subgroup.normalizer (image : Set group)) kernel,
    sup_assoc, sup_eq_left.mpr Subgroup.le_normalizer] at frattini
  exact frattini

theorem exists_sylow_intersection_normal {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (normal : Subgroup group) [normal.Normal]
    (sylow : Sylow prime group) :
    ∃ internal : Sylow prime normal,
      (internal : Subgroup normal).map normal.subtype = (sylow : Subgroup group) ⊓ normal := by
  have intersection_prime : IsPGroup prime ((sylow : Subgroup group).subgroupOf normal) :=
    sylow.isPGroup'.comap_of_injective normal.subtype Subtype.val_injective
  obtain ⟨internal, contains⟩ := intersection_prime.exists_le_sylow
  obtain ⟨ambient, ambient_eq⟩ := internal.exists_comap_subtype_eq
  obtain ⟨conjugator, conjugates⟩ := MulAction.exists_smul_eq group ambient sylow
  have conjugate_eq : ((ambient : Subgroup group) ⊓ normal).map (MulAut.conj conjugator).toMonoidHom =
      (sylow : Subgroup group) ⊓ normal := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj conjugator).injective]
    have sylow_eq := congrArg (fun current : Sylow prime group => (current : Subgroup group)) conjugates
    rw [Sylow.coe_subgroup_smul] at sylow_eq
    change (ambient : Subgroup group).map (MulAut.conj conjugator).toMonoidHom = sylow at sylow_eq
    have normal_eq := Subgroup.Normal.map_conj_eq normal conjugator
    change normal.map (MulAut.conj conjugator).toMonoidHom = normal at normal_eq
    rw [sylow_eq, normal_eq]
  have intersection_card : Nat.card ↥((ambient : Subgroup group) ⊓ normal) =
      Nat.card ↥((sylow : Subgroup group) ⊓ normal) := by
    rw [← Subgroup.card_map_of_injective (K := (ambient : Subgroup group) ⊓ normal)
      (f := (MulAut.conj conjugator).toMonoidHom)
      (MulAut.conj conjugator).injective, conjugate_eq]
  have internal_card : Nat.card (internal : Subgroup normal) =
      Nat.card ((sylow : Subgroup group).subgroupOf normal) := by
    rw [← ambient_eq]
    change Nat.card ((ambient : Subgroup group).subgroupOf normal) = _
    rw [CFSG.OrderReductions.ReplacementGeometry.card_subgroupOf_eq_intersection,
      CFSG.OrderReductions.ReplacementGeometry.card_subgroupOf_eq_intersection, inf_comm normal (ambient : Subgroup group),
      inf_comm normal (sylow : Subgroup group)]
    exact intersection_card
  have equal := Subgroup.eq_of_le_of_card_ge contains internal_card.le
  refine ⟨internal, ?_⟩
  rw [← equal]
  exact Subgroup.subgroupOf_map_subtype _ _

theorem actionCore_frattini {actors target : Type*} [Group actors] [Finite actors] [Group target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (action : actors →* MulAut target)
    (sylow : Sylow prime (CFSG.OrderReductions.ActionPrimeCore.actionCore prime action)) :
    action.ker ⊔ (sylow : Subgroup (CFSG.OrderReductions.ActionPrimeCore.actionCore prime action)).map
        (CFSG.OrderReductions.ActionPrimeCore.actionCore prime action).subtype = CFSG.OrderReductions.ActionPrimeCore.actionCore prime action ∧
      action.ker ⊔ Subgroup.normalizer
        (((sylow : Subgroup (CFSG.OrderReductions.ActionPrimeCore.actionCore prime action)).map
          (CFSG.OrderReductions.ActionPrimeCore.actionCore prime action).subtype) : Set actors) = ⊤ :=
  normal_prime_quotient_frattini prime action.ker (CFSG.OrderReductions.ActionPrimeCore.actionCore prime action)
    (CFSG.OrderReductions.ActionPrimeCore.kernel_le_actionCore prime action)
    (CFSG.OrderReductions.ActionPrimeCore.actionCore_quotient_isPGroup prime action) sylow

end CFSG.OrderReductions.PrimeQuotientFrattini
