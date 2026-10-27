module

public import CFSG.LocalAnalysis.ComponentClassification.BlockProperTwoAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockCrossRankBound

theorem bound {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hmutualEven : ∀ third ∈ UniversalOrbitBlock.block component,
      Even (Nat.card ↥(UniversalOrbitBlock.conjugate third actor ⊓ Subgroup.normalizer (first : Set G)))) :
    pRank 2 (UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component) ≤
      pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) := by
  classical
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨other, hotherSecond, _⟩ := ComponentFamilyPumpUpFusion.exists_outside_two
    hfamilyCard (⟨second, hsecond⟩ : Index) (⟨second, hsecond⟩ : Index)
  let firstMutual := UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G)
  let secondMutual := UniversalOrbitBlock.conjugate other.val actor ⊓ Subgroup.normalizer (first : Set G)
  let firstSylow : Sylow 2 firstMutual := Classical.choice inferInstance
  let secondSylow : Sylow 2 secondMutual := Classical.choice inferInstance
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
    have hdivides := firstSylow.dvd_card_of_dvd_card (even_iff_two_dvd.mp (hmutualEven second hsecond))
    rw [hcardOne] at hdivides
    norm_num at hdivides
  obtain ⟨hab, homomorphism, hinjective⟩ := BlockProperTwoAction.abelian_embedding component heven huniversal hquasisimple
    hcard hcontrol first second other.val hfirst hsecond other.property
      (fun heq => hotherSecond (Subtype.ext heq.symm)) actor hactor firstTwo secondTwo hfirstTwo hsecondTwo hfirstNe
        (hfirstMutual.trans inf_le_left) (hsecondMutual.trans inf_le_left)
        (hfirstMutual.trans inf_le_right) (hsecondMutual.trans inf_le_right)
  have hfirstRank : pRank 2 firstTwo = pRank 2 firstMutual :=
    InvolutionGeneratedSubgroup.sylow_rank_eq firstMutual firstSylow
  have hbound : pRank 2 firstTwo ≤
      pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) := by
    have hfirstJoin := TwoRankTransport.mono (le_sup_left : firstTwo ≤ firstTwo ⊔ secondTwo)
    have hjoin := TwoRankTransport.injective homomorphism hinjective
    rw [TwoRankTransport.subgroup, TwoRankTransport.subgroup] at hjoin
    exact hfirstJoin.trans hjoin
  rw [hfirstRank, BlockMutualRanks.right component heven huniversal hquasisimple hcard hcontrol first second
    hfirst hsecond actor hactor] at hbound
  exact hbound

end CFSG.ComponentClassification.BlockCrossRankBound
