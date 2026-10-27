module

public import CFSG.LocalAnalysis.ComponentClassification.CommonInvolutionSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.BlockReversedMutualEven

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockCommonInvolutions

theorem right {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (hmutualEven : ∀ first ∈ UniversalOrbitBlock.block component, ∀ second ∈ UniversalOrbitBlock.block component,
      Even (Nat.card ↥(first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G))) ∧
        Even (Nat.card ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G))))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component) :
    ∃ elementary : Subgroup G, IsElemAbelian 2 elementary ∧
      Nat.card elementary = 2 ^ pRank 2 (first ⊓
        (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) ∧
      (∀ second ∈ UniversalOrbitBlock.block component,
        elementary ≤ UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component) ∧
      (∀ second ∈ UniversalOrbitBlock.block component, ∀ member : G,
        member ∈ UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component ∧
          orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1) := by
  classical
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
  let normalizers := fun index : Index => UniversalOrbitBlock.conjugate index.val actor ⊓ Subgroup.normalizer (first : Set G)
  let overlaps := fun index : Index => UniversalOrbitBlock.conjugate index.val actor ⊓ UniversalOrbitBlock.normalizer component
  let rank := pRank 2 (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
  have hcontained : ∀ index, normalizers index ≤ overlaps index := by
    intro index
    exact inf_le_inf_left _ (UniversalOrbitBlock.factor_normalizer_le component heven huniversal hquasisimple first hfirst)
  have hcoverage : ∀ index, ∀ member ∈ overlaps index, orderOf member = 2 → member ∈ normalizers index := by
    intro index member hmember horder
    exact ⟨hmember.1, BlockMutualRanks.image_involution_normalizes component heven huniversal hcard hcontrol first index.val
      hfirst index.property actor hactor member hmember horder⟩
  have hrank : ∀ index, pRank 2 (normalizers index) = rank := by
    intro index
    rw [BlockMutualRanks.right component heven huniversal hquasisimple hcard hcontrol first index.val hfirst index.property
      actor hactor]
    exact (BlockCommonRank.equal component heven huniversal hquasisimple hcard hcontrol actor hactor hmutualEven first
      index.val hfirst index.property).symm
  have hpair : ∀ left right : Index, left ≠ right →
      ∀ leftSylow : Sylow 2 (normalizers left), ∀ rightSylow : Sylow 2 (normalizers right),
        IsMulCommutative ↥(CommonInvolutionSubgroup.sylowImage (normalizers left) leftSylow ⊔
          CommonInvolutionSubgroup.sylowImage (normalizers right) rightSylow) ∧
        InvolutionGeneratedSubgroup.omega (CommonInvolutionSubgroup.sylowImage (normalizers left) leftSylow) =
          InvolutionGeneratedSubgroup.omega (CommonInvolutionSubgroup.sylowImage (normalizers right) rightSylow) := by
    intro left right hne leftSylow rightSylow
    have hpair := BlockPairSylowOmega.pair component heven huniversal hquasisimple hcard hcontrol actor hactor hmutualEven
      first left.val right.val hfirst left.property right.property (fun heq => hne (Subtype.ext heq)) leftSylow rightSylow
    exact ⟨hpair.1, hpair.2.1⟩
  obtain ⟨elementary, helementary, hsize, hle, _, hcharacterization⟩ := CommonInvolutionSubgroup.exists_common hfamilyCard
    normalizers overlaps hcontained hcoverage rank hrank hpair
  exact ⟨elementary, helementary, hsize, fun second hsecond => hle ⟨second, hsecond⟩,
    fun second hsecond => hcharacterization ⟨second, hsecond⟩⟩

theorem left {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (hmutualEven : ∀ first ∈ UniversalOrbitBlock.block component, ∀ second ∈ UniversalOrbitBlock.block component,
      Even (Nat.card ↥(first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G))) ∧
        Even (Nat.card ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G))))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component) :
    ∃ elementary : Subgroup G, IsElemAbelian 2 elementary ∧
      Nat.card elementary = 2 ^ pRank 2 (first ⊓
        (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) ∧
      (∀ second ∈ UniversalOrbitBlock.block component,
        elementary ≤ second ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) ∧
      (∀ second ∈ UniversalOrbitBlock.block component, ∀ member : G,
        member ∈ second ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ∧
          orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1) := by
  let conjugateComponent := UniversalOrbitBlock.conjugate component actor
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hconjugateEven := UniversalOrbitBlock.orbit_even component heven conjugateComponent horbit
  have hconjugateUniversal := UniversalOrbitBlock.orbit_universal component huniversal conjugateComponent horbit
  have hconjugateQuasisimple := UniversalOrbitBlock.orbit_quasisimple component hquasisimple conjugateComponent horbit
  have hconjugateCard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block conjugateComponent) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have hconjugateControl := BlockExternalControlConjugation.control component actor hcontrol
  have hconjugateOutside := OrbitBlockConjugation.inverse_outside component actor hactor
  obtain ⟨elementary, helementary, hsize, hle, hcharacterization⟩ := right conjugateComponent hconjugateEven
    hconjugateUniversal hconjugateQuasisimple hconjugateCard hconjugateControl actor⁻¹ hconjugateOutside
      (BlockReversedMutualEven.even component actor hmutualEven) conjugateComponent
        (UniversalOrbitBlock.mem_block_self conjugateComponent)
  have hnormalizerBack : (UniversalOrbitBlock.normalizer conjugateComponent).map (MulAut.conj actor⁻¹).toMonoidHom =
      UniversalOrbitBlock.normalizer component := by
    rw [OrbitBlockConjugation.normalizer]
    change UniversalOrbitBlock.normalizer
      (UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate component actor) actor⁻¹) = _
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one]
  rw [hnormalizerBack, ← BlockCommonRank.equal component heven huniversal hquasisimple hcard hcontrol actor hactor
    hmutualEven first component hfirst (UniversalOrbitBlock.mem_block_self component)] at hsize
  refine ⟨elementary, helementary, hsize, ?_, ?_⟩
  · intro second hsecond
    have hmem := hle (UniversalOrbitBlock.conjugate second actor)
      ((OrbitBlockConjugation.block component second actor).mpr hsecond)
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one,
      ← OrbitBlockConjugation.normalizer component actor] at hmem
    exact hmem
  · intro second hsecond member
    have hmem := hcharacterization (UniversalOrbitBlock.conjugate second actor)
      ((OrbitBlockConjugation.block component second actor).mpr hsecond) member
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one,
      ← OrbitBlockConjugation.normalizer component actor] at hmem
    exact hmem

end CFSG.ComponentClassification.BlockCommonInvolutions
