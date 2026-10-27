module

public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAbelian

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockStrictFullSylowAbelian

theorem original {G : Type*} [Group G] [Finite G]
    {component fixed elementary opposite : Subgroup G} {actor : G} {rank : ℕ}
    (context : BlockFixedFactorSylowReduction.Context component actor fixed rank elementary opposite)
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (sylow : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) :
    IsMulCommutative ((sylow : Subgroup ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
        (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype) := by
  classical
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using context.card
  obtain ⟨second, hsecond, _⟩ := ComponentFamilyPumpUpFusion.exists_outside_two hfamilyCard
    (⟨first, hfirst⟩ : Index) (⟨first, hfirst⟩ : Index)
  let firstOverlap := first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let firstTwo := (sylow : Subgroup firstOverlap).map firstOverlap.subtype
  have hbound : firstTwo ≤ firstOverlap := Subgroup.map_subtype_le _
  have hab := BlockTwoProductAbelian.reverse component context.even context.universal context.quasisimple context.card
    context.control first second.val fixed hfirst second.property context.fixed_mem (fun heq => hsecond (Subtype.ext heq.symm))
      actor context.outside firstTwo ⊥ (sylow.isPGroup'.map firstOverlap.subtype) (by
        intro member
        exact ⟨0, Subsingleton.elim _ _⟩)
          (BlockCommonSylowNontrivial.image_ne_bot context.original context.positive first hfirst sylow)
            (hbound.trans inf_le_left) bot_le (hbound.trans (context.normalizes first hfirst)) bot_le context.reverse_strict
  exact BlockPairSylowOmega.abelian_of_le (le_sup_left : firstTwo ≤ firstTwo ⊔ ⊥) hab

theorem opposite {G : Type*} [Group G] [Finite G]
    {component fixed elementary opposite : Subgroup G} {actor : G} {rank : ℕ}
    (context : BlockFixedFactorSylowReduction.Context component actor fixed rank elementary opposite)
    (second : Subgroup G) (hsecond : second ∈ UniversalOrbitBlock.block component)
    (sylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component)) :
    IsMulCommutative ((sylow : Subgroup ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component)).map
      (UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component).subtype) := by
  classical
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using context.card
  obtain ⟨third, hthird, _⟩ := ComponentFamilyPumpUpFusion.exists_outside_two hfamilyCard
    (⟨second, hsecond⟩ : Index) (⟨second, hsecond⟩ : Index)
  let overlap := UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component
  let image := (sylow : Subgroup overlap).map overlap.subtype
  have hbound : image ≤ overlap := Subgroup.map_subtype_le _
  obtain ⟨first, hfirst, hnormalizes⟩ := OddBlockSylowAbelian.fixed_factor component context.even context.universal context.quasisimple
    context.odd image (sylow.isPGroup'.map overlap.subtype) (hbound.trans inf_le_right)
  have hab := BlockTwoProductAbelian.forward component context.even context.universal context.quasisimple context.card
    context.control first second third.val hfirst hsecond third.property (fun heq => hthird (Subtype.ext heq.symm)) actor context.outside
      image ⊥ (sylow.isPGroup'.map overlap.subtype) (by
        intro member
        exact ⟨0, Subsingleton.elim _ _⟩)
          (BlockCommonSylowNontrivial.image_ne_bot context.opposite context.positive (UniversalOrbitBlock.conjugate second actor)
            ((OrbitBlockConjugation.block component second actor).mpr hsecond) sylow)
              (hbound.trans inf_le_left) bot_le hnormalizes bot_le (context.forward_strict first hfirst)
  exact BlockPairSylowOmega.abelian_of_le (le_sup_left : image ≤ image ⊔ ⊥) hab

end CFSG.ComponentClassification.BlockStrictFullSylowAbelian
