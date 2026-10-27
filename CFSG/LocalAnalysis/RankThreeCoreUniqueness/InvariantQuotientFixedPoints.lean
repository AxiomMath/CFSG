module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeNonabelian

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem action_invariant_subgroup_map_eq
    {Actor Value : Type*} [Group Actor] [Group Value]
    (action : Actor →* MulAut Value) (invariantGroup : Subgroup Value)
    (hinvariant : ∀ actingElement : Actor, ∀ element ∈ invariantGroup,
      action actingElement element ∈ invariantGroup) (actingElement : Actor) :
    Subgroup.map (action actingElement : Value →* Value) invariantGroup = invariantGroup := by
  apply le_antisymm
  · rintro element ⟨preimage, hpreimage, rfl⟩
    exact hinvariant actingElement preimage hpreimage
  · intro element helement
    refine ⟨action actingElement⁻¹ element, hinvariant actingElement⁻¹ element helement, ?_⟩
    rw [map_inv]
    exact MulAut.apply_inv_self _ _ _

@[expose] def invariantQuotientActionHom
    {Actor Value : Type*} [Group Actor] [Group Value]
    (action : Actor →* MulAut Value) (invariantGroup : Subgroup Value)
    [invariantGroup.Normal]
    (hinvariant : ∀ actingElement : Actor, ∀ element ∈ invariantGroup,
      action actingElement element ∈ invariantGroup) : Actor →* MulAut (Value ⧸ invariantGroup) where
  toFun actingElement := QuotientGroup.congr invariantGroup invariantGroup (action actingElement)
    (action_invariant_subgroup_map_eq action invariantGroup hinvariant actingElement)
  map_one' := by
    ext element
    obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective invariantGroup element
    simp only [QuotientGroup.congr_mk', map_one, MulAut.one_apply]
  map_mul' := by
    intro first second
    ext element
    obtain ⟨preimage, rfl⟩ := QuotientGroup.mk'_surjective invariantGroup element
    change (QuotientGroup.congr invariantGroup invariantGroup (action (first * second))
        (action_invariant_subgroup_map_eq action invariantGroup hinvariant (first * second)))
        ((QuotientGroup.mk' invariantGroup) preimage) =
      (QuotientGroup.congr invariantGroup invariantGroup (action first)
        (action_invariant_subgroup_map_eq action invariantGroup hinvariant first))
        ((QuotientGroup.congr invariantGroup invariantGroup (action second)
          (action_invariant_subgroup_map_eq action invariantGroup hinvariant second))
          ((QuotientGroup.mk' invariantGroup) preimage))
    rw [QuotientGroup.congr_mk', QuotientGroup.congr_mk', QuotientGroup.congr_mk', map_mul]
    rfl

theorem invariantQuotientActionHom_mk
    {Actor Value : Type*} [Group Actor] [Group Value]
    (action : Actor →* MulAut Value) (invariantGroup : Subgroup Value)
    [invariantGroup.Normal]
    (hinvariant : ∀ actingElement : Actor, ∀ element ∈ invariantGroup,
      action actingElement element ∈ invariantGroup) (actingElement : Actor) (element : Value) :
    invariantQuotientActionHom action invariantGroup hinvariant actingElement
      ((QuotientGroup.mk' invariantGroup) element) =
        (QuotientGroup.mk' invariantGroup) (action actingElement element) := by
  exact QuotientGroup.congr_mk' invariantGroup invariantGroup (action actingElement)
    (action_invariant_subgroup_map_eq action invariantGroup hinvariant actingElement) element

theorem coprime_normal_quotient_fixed_lift
    {Actor Value : Type*} [Group Actor] [Group Value] [Finite Value]
    (prime : ℕ) (hprime : prime.Prime) (hactor : IsPGroup prime Actor)
    (action : Actor →* MulAut Value) (invariantGroup : Subgroup Value)
    [invariantGroup.Normal]
    (hinvariant : ∀ actingElement : Actor, ∀ element ∈ invariantGroup,
      action actingElement element ∈ invariantGroup)
    (hcoprime : prime.Coprime (Nat.card invariantGroup))
    (element : Value ⧸ invariantGroup)
    (hfixed : ∀ actingElement : Actor,
      invariantQuotientActionHom action invariantGroup hinvariant actingElement element = element) :
    ∃ preimage : Value, (QuotientGroup.mk' invariantGroup) preimage = element ∧
      ∀ actingElement : Actor, action actingElement preimage = preimage := by
  let : MulDistribMulAction Actor Value := multiplicativeActionOfMulAutHom action
  let : MulDistribMulAction Actor (Value ⧸ invariantGroup) :=
    multiplicativeActionOfMulAutHom (invariantQuotientActionHom action invariantGroup hinvariant)
  apply coprime_pGroup_fixed_lift prime hprime hactor (QuotientGroup.mk' invariantGroup)
    (QuotientGroup.mk'_surjective invariantGroup) _ _ element hfixed
  · intro actingElement preimage
    exact (invariantQuotientActionHom_mk action invariantGroup hinvariant actingElement preimage).symm
  · rwa [QuotientGroup.ker_mk']

instance pair_intersection_internal_normalizer_normal
    {G : Type*} [Group G] (first second : Subgroup G) :
    ((first ⊓ second).subgroupOf
      (first ⊓ Subgroup.normalizer ((first ⊓ second : Subgroup G) : Set G))).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer inf_le_right

end CFSG.RankThreeCoreUniqueness.Helpers
