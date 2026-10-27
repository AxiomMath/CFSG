module

public import CFSG.LocalAnalysis.ComponentClassification.BlockCommonRank

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockPairSylowOmega

theorem abelian_of_le {G : Type*} [Group G] {first second : Subgroup G}
    (hle : first ≤ second) (hab : IsMulCommutative second) : IsMulCommutative first := by
  apply isMulCommutative_iff.mpr
  intro left right
  apply Subtype.ext
  change left.val * right.val = right.val * left.val
  exact congrArg Subtype.val (isMulCommutative_iff.mp hab
    (⟨left.val, hle left.property⟩ : second) (⟨right.val, hle right.property⟩ : second))

theorem pair {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (hmutualEven : ∀ first ∈ UniversalOrbitBlock.block component, ∀ second ∈ UniversalOrbitBlock.block component,
      Even (Nat.card ↥(first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G))) ∧
        Even (Nat.card ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G))))
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (firstSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)))
    (secondSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G))) :
    let firstMutual := UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)
    let secondMutual := UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)
    let firstTwo := (firstSylow : Subgroup firstMutual).map firstMutual.subtype
    let secondTwo := (secondSylow : Subgroup secondMutual).map secondMutual.subtype
    IsMulCommutative ↥(firstTwo ⊔ secondTwo) ∧
      InvolutionGeneratedSubgroup.omega firstTwo = InvolutionGeneratedSubgroup.omega secondTwo ∧
      pRank 2 (firstTwo ⊔ secondTwo) =
        pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) := by
  let firstMutual := UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)
  let secondMutual := UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)
  let firstTwo := (firstSylow : Subgroup firstMutual).map firstMutual.subtype
  let secondTwo := (secondSylow : Subgroup secondMutual).map secondMutual.subtype
  have hfirstMutual : firstTwo ≤ firstMutual := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hsecondMutual : secondTwo ≤ secondMutual := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have hfirstTwo : IsPGroup 2 firstTwo := firstSylow.isPGroup'.map firstMutual.subtype
  have hsecondTwo : IsPGroup 2 secondTwo := secondSylow.isPGroup'.map secondMutual.subtype
  have hfirstNe : firstTwo ≠ ⊥ := by
    intro hbot
    have hcardOne : Nat.card firstTwo = 1 := firstTwo.eq_bot_iff_card.mp hbot
    rw [Subgroup.card_map_of_injective firstMutual.subtype_injective] at hcardOne
    have hdivides := firstSylow.dvd_card_of_dvd_card (even_iff_two_dvd.mp (hmutualEven first hfirst second hsecond).2)
    rw [hcardOne] at hdivides
    norm_num at hdivides
  obtain ⟨hab, homomorphism, hinjective⟩ := BlockProperTwoAction.abelian_embedding component heven huniversal hquasisimple
    hcard hcontrol first second third hfirst hsecond hthird hdistinct actor hactor firstTwo secondTwo
      hfirstTwo hsecondTwo hfirstNe (hfirstMutual.trans inf_le_left) (hsecondMutual.trans inf_le_left)
        (hfirstMutual.trans inf_le_right) (hsecondMutual.trans inf_le_right)
  have hfirstRank : pRank 2 firstTwo =
      pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) := by
    rw [InvolutionGeneratedSubgroup.sylow_rank_eq firstMutual firstSylow,
      BlockMutualRanks.right component heven huniversal hquasisimple hcard hcontrol first second hfirst hsecond actor hactor]
    exact (BlockCommonRank.equal component heven huniversal hquasisimple hcard hcontrol actor hactor hmutualEven
      first second hfirst hsecond).symm
  have hsecondRank : pRank 2 secondTwo =
      pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) := by
    rw [InvolutionGeneratedSubgroup.sylow_rank_eq secondMutual secondSylow,
      BlockMutualRanks.right component heven huniversal hquasisimple hcard hcontrol first third hfirst hthird actor hactor]
    exact (BlockCommonRank.equal component heven huniversal hquasisimple hcard hcontrol actor hactor hmutualEven
      first third hfirst hthird).symm
  have hjoinRank : pRank 2 (firstTwo ⊔ secondTwo) =
      pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) := by
    apply le_antisymm
    · have hbound := TwoRankTransport.injective homomorphism hinjective
      rwa [TwoRankTransport.subgroup, TwoRankTransport.subgroup] at hbound
    · rw [← hfirstRank]
      exact TwoRankTransport.mono le_sup_left
  have hfirstAb : IsMulCommutative firstTwo := abelian_of_le le_sup_left hab
  have hsecondAb : IsMulCommutative secondTwo := abelian_of_le le_sup_right hab
  have hfirstOmega := InvolutionGeneratedSubgroup.eq_of_rank hfirstAb hab le_sup_left (hfirstRank.trans hjoinRank.symm)
  have hsecondOmega := InvolutionGeneratedSubgroup.eq_of_rank hsecondAb hab le_sup_right (hsecondRank.trans hjoinRank.symm)
  exact ⟨hab, hfirstOmega.trans hsecondOmega.symm, hjoinRank⟩

end CFSG.ComponentClassification.BlockPairSylowOmega
