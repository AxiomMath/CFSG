module

public import CFSG.LocalAnalysis.ComponentClassification.BlockTransitivity
public import CFSG.LocalAnalysis.ComponentClassification.InnerActionOrder
public import CFSG.LocalAnalysis.ComponentClassification.GroupTwoPart

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockNormalizerOrder

@[expose] noncomputable def action {G : Type*} [Group G] (component : Subgroup G) :
    Subgroup.normalizer (component : Set G) →* MulAut (component ⧸ Subgroup.center component) :=
  (PerfectAutomorphisms.centerQuotientHom component).comp component.normalizerMonoidHom

theorem kernel {G : Type*} [Group G] (component : Subgroup G) (hquasisimple : IsQuasisimple component) :
    (action component).ker = (Subgroup.centralizer (component : Set G)).subgroupOf (Subgroup.normalizer (component : Set G)) := by
  let : Group.IsPerfect component := ⟨hquasisimple.1⟩
  exact (MonoidHom.ker_comp_of_injective component.normalizerMonoidHom (PerfectAutomorphisms.centerQuotientHom component)
    (PerfectAutomorphisms.centerQuotientHom_injective component)).trans (Subgroup.normalizerMonoidHom_ker component)

theorem card {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component) :
    Nat.card (UniversalOrbitBlock.normalizer component) = Nat.card (Subgroup.centralizer (component : Set G)) *
      Nat.card (action component).range * Nat.card ↥(UniversalOrbitBlock.block component) := by
  have hkernelCard : Nat.card (action component).ker = Nat.card (Subgroup.centralizer (component : Set G)) := by
    rw [kernel component hquasisimple]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)).toEquiv
  have hnormalizerCard := (action component).ker.card_mul_index
  rw [Subgroup.index_ker, hkernelCard] at hnormalizerCard
  rw [BlockTransitivity.card component heven huniversal hquasisimple component (UniversalOrbitBlock.mem_block_self component),
    ← hnormalizerCard]

theorem inner_le {G : Type*} [Group G] (component : Subgroup G) :
    OuterAutomorphisms.inner (component ⧸ Subgroup.center component) ≤ (action component).range := by
  rintro automorphism ⟨element, rfl⟩
  obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center component) element
  let actor : Subgroup.normalizer (component : Set G) := ⟨lift.val, Subgroup.le_normalizer lift.property⟩
  refine ⟨actor, ?_⟩
  have hnormalizer : component.normalizerMonoidHom actor = MulAut.conj lift := by
    ext member
    rfl
  change PerfectAutomorphisms.centerQuotientHom component (component.normalizerMonoidHom actor) = _
  rw [hnormalizer, OuterAutomorphisms.centerQuotient_conj]

theorem image_two_bound {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hquasisimple : IsQuasisimple component) :
    GroupTwoPart.value (Nat.card (action component).range) ≤
      GroupTwoPart.value (Nat.card (component ⧸ Subgroup.center component)) *
        GroupTwoPart.value (Nat.card (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) := by
  let quotient := component ⧸ Subgroup.center component
  let : IsSimpleGroup quotient := hquasisimple.2
  have hcenter : Subgroup.center quotient = ⊥ := Helpers.center_eq_bot quotient
    (Helpers.quasisimple_central_quotient_nonabelian component hquasisimple)
  have hcard := InnerActionOrder.image_card (action component).range (inner_le component)
  rw [InnerActionOrder.centerless_card quotient hcenter] at hcard
  rw [hcard, GroupTwoPart.mul (ne_of_gt Nat.card_pos) (ne_of_gt Nat.card_pos)]
  exact Nat.mul_le_mul_left _ (GroupTwoPart.subgroup_le _)

theorem two_bound {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component) :
    GroupTwoPart.value (Nat.card (UniversalOrbitBlock.normalizer component)) ≤
      GroupTwoPart.value (Nat.card ↥(UniversalOrbitBlock.block component)) *
        GroupTwoPart.value (Nat.card (Subgroup.centralizer (component : Set G))) *
        GroupTwoPart.value (Nat.card (component ⧸ Subgroup.center component)) *
        GroupTwoPart.value (Nat.card (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) := by
  let centralOrder := Nat.card (Subgroup.centralizer (component : Set G))
  let imageOrder := Nat.card (action component).range
  let blockOrder := Nat.card ↥(UniversalOrbitBlock.block component)
  have hcentralPositive : centralOrder ≠ 0 := ne_of_gt (Nat.card_pos (α := Subgroup.centralizer (component : Set G)))
  have himagePositive : imageOrder ≠ 0 := ne_of_gt (Nat.card_pos (α := (action component).range))
  have hblockPositive : blockOrder ≠ 0 := by
    let : Nonempty ↥(UniversalOrbitBlock.block component) := ⟨⟨component, UniversalOrbitBlock.mem_block_self component⟩⟩
    exact ne_of_gt (Nat.card_pos (α := ↥(UniversalOrbitBlock.block component)))
  have hcard : Nat.card (UniversalOrbitBlock.normalizer component) = centralOrder * imageOrder * blockOrder :=
    card component heven huniversal hquasisimple
  have hparts : GroupTwoPart.value (centralOrder * imageOrder * blockOrder) =
      GroupTwoPart.value centralOrder * GroupTwoPart.value imageOrder * GroupTwoPart.value blockOrder := by
    rw [GroupTwoPart.mul (mul_ne_zero hcentralPositive himagePositive) hblockPositive,
      GroupTwoPart.mul hcentralPositive himagePositive]
  have hexact := (congrArg GroupTwoPart.value hcard).trans hparts
  have hbound := Nat.mul_le_mul_right (GroupTwoPart.value blockOrder)
    (Nat.mul_le_mul_left (GroupTwoPart.value centralOrder) (image_two_bound component hquasisimple))
  exact hexact.le.trans (hbound.trans_eq (by dsimp [centralOrder, blockOrder]; ac_rfl))

end CFSG.ComponentClassification.BlockNormalizerOrder
