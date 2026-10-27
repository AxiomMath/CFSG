module

public import CFSG.LocalAnalysis.ComponentClassification.OddBlockSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.BlockCommonSylowNontrivial
public import CFSG.LocalAnalysis.ComponentClassification.BlockPairOrderBounds

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockFixedFactorSizeSandwich

theorem upper {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (fixed : Subgroup G) (hfixed : fixed ∈ UniversalOrbitBlock.block component)
    (hnormalizes : ∀ first ∈ UniversalOrbitBlock.block component,
      first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ≤
        Subgroup.normalizer (UniversalOrbitBlock.conjugate fixed actor : Set G))
    (rank : ℕ) (hpositive : 1 ≤ rank) (elementary : Subgroup G)
    (properties : BlockCommonInvolutionPackage.Common component
      ((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) rank elementary)
    (hstrict : ∀ left : Sylow 2 ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component),
      ∀ right : Sylow 2 (UniversalOrbitBlock.conjugate fixed actor),
        Nat.card (left : Subgroup ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component)) <
          Nat.card (right : Subgroup (UniversalOrbitBlock.conjugate fixed actor)))
    (prescribed : Sylow 2 ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (sylow : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) :
    Nat.card (sylow : Subgroup ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) ≤
      Nat.card (prescribed : Subgroup ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component)) := by
  classical
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨other, hother, _⟩ := ComponentFamilyPumpUpFusion.exists_outside_two hfamilyCard
    (⟨first, hfirst⟩ : Index) (⟨first, hfirst⟩ : Index)
  let firstOverlap := first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let secondOverlap := other.val ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let secondSylow : Sylow 2 secondOverlap := Classical.choice inferInstance
  let firstTwo := (sylow : Subgroup firstOverlap).map firstOverlap.subtype
  let secondTwo := (secondSylow : Subgroup secondOverlap).map secondOverlap.subtype
  have hfirstBound : firstTwo ≤ firstOverlap := Subgroup.map_subtype_le _
  have hsecondBound : secondTwo ≤ secondOverlap := Subgroup.map_subtype_le _
  have hbound := BlockPairOrderBounds.reverse component heven huniversal hquasisimple hcard hcontrol
    first other.val fixed hfirst other.property hfixed (fun heq => hother (Subtype.ext heq.symm)) actor hactor
      firstTwo secondTwo (sylow.isPGroup'.map firstOverlap.subtype) (secondSylow.isPGroup'.map secondOverlap.subtype)
        (BlockCommonSylowNontrivial.image_ne_bot properties hpositive first hfirst sylow)
          (hfirstBound.trans inf_le_left) (hsecondBound.trans inf_le_left)
            (hfirstBound.trans (hnormalizes first hfirst)) (hsecondBound.trans (hnormalizes other.val other.property))
              hstrict prescribed
  have hfirstCard := (Subgroup.card_le_of_le (le_sup_left : firstTwo ≤ firstTwo ⊔ secondTwo)).trans hbound
  simpa only [firstTwo, Subgroup.card_map_of_injective firstOverlap.subtype_injective] using hfirstCard

theorem lower {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hodd : Odd (Nat.card ↥(UniversalOrbitBlock.block component)))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (fixed moved : Subgroup G) (hfixed : fixed ∈ UniversalOrbitBlock.block component)
    (hmoved : moved ∈ UniversalOrbitBlock.block component) (hdistinct : fixed ≠ moved)
    (rank : ℕ) (hpositive : 1 ≤ rank) (elementary : Subgroup G)
    (properties : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
      (UniversalOrbitBlock.normalizer component) rank elementary)
    (hstrict : ∀ first ∈ UniversalOrbitBlock.block component,
      ∀ left : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom),
      ∀ right : Sylow 2 first,
        Nat.card (left : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
            Nat.card (right : Subgroup first))
    (fixedSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component))
    (movedSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate moved actor ⊓ UniversalOrbitBlock.normalizer component)) :
    ∃ first ∈ UniversalOrbitBlock.block component,
      ∀ prescribed : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom),
        Nat.card ↥((fixedSylow : Subgroup ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component)).map
            (UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component).subtype ⊔
          (movedSylow : Subgroup ↥(UniversalOrbitBlock.conjugate moved actor ⊓ UniversalOrbitBlock.normalizer component)).map
            (UniversalOrbitBlock.conjugate moved actor ⊓ UniversalOrbitBlock.normalizer component).subtype) ≤
          Nat.card (prescribed : Subgroup ↥(first ⊓
            (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) := by
  let fixedOverlap := UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component
  let movedOverlap := UniversalOrbitBlock.conjugate moved actor ⊓ UniversalOrbitBlock.normalizer component
  let firstTwo := (fixedSylow : Subgroup fixedOverlap).map fixedOverlap.subtype
  let secondTwo := (movedSylow : Subgroup movedOverlap).map movedOverlap.subtype
  have hfirstBound : firstTwo ≤ fixedOverlap := Subgroup.map_subtype_le _
  have hsecondBound : secondTwo ≤ movedOverlap := Subgroup.map_subtype_le _
  have hfirstTwo : IsPGroup 2 firstTwo := fixedSylow.isPGroup'.map fixedOverlap.subtype
  have hsecondTwo : IsPGroup 2 secondTwo := movedSylow.isPGroup'.map movedOverlap.subtype
  have hcommutes : ⁅firstTwo, secondTwo⁆ = ⊥ := by
    have hmap := congrArg (Subgroup.map (MulAut.conj actor).toMonoidHom)
      (UniversalOrbitBlock.block_commutes component heven huniversal fixed hfixed moved hmoved hdistinct)
    have himages : ⁅UniversalOrbitBlock.conjugate fixed actor, UniversalOrbitBlock.conjugate moved actor⁆ = ⊥ := by
      change ⁅fixed.map (MulAut.conj actor).toMonoidHom, moved.map (MulAut.conj actor).toMonoidHom⁆ = ⊥
      simpa only [Subgroup.map_commutator, Subgroup.map_bot] using hmap
    apply le_antisymm _ bot_le
    rw [← himages]
    exact Subgroup.commutator_mono (hfirstBound.trans inf_le_left) (hsecondBound.trans inf_le_left)
  obtain ⟨first, hfirst, hnormalizes⟩ := OddBlockSylowAbelian.fixed_factor component heven huniversal hquasisimple hodd
    (firstTwo ⊔ secondTwo) (BlockTwoProductAction.two_join firstTwo secondTwo hfirstTwo hsecondTwo hcommutes)
      (sup_le (hfirstBound.trans inf_le_right) (hsecondBound.trans inf_le_right))
  refine ⟨first, hfirst, ?_⟩
  intro prescribed
  exact BlockPairOrderBounds.forward component heven huniversal hquasisimple hcard hcontrol
    first fixed moved hfirst hfixed hmoved hdistinct actor hactor firstTwo secondTwo hfirstTwo hsecondTwo
      (BlockCommonSylowNontrivial.image_ne_bot properties hpositive (UniversalOrbitBlock.conjugate fixed actor)
        ((OrbitBlockConjugation.block component fixed actor).mpr hfixed) fixedSylow)
          (hfirstBound.trans inf_le_left) (hsecondBound.trans inf_le_left)
            (le_sup_left.trans hnormalizes) (le_sup_right.trans hnormalizes) (hstrict first hfirst) prescribed

end CFSG.ComponentClassification.BlockFixedFactorSizeSandwich
