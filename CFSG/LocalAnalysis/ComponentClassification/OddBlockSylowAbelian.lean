module

public import CFSG.LocalAnalysis.ComponentClassification.BlockPairSylowOmega
public import CFSG.LocalAnalysis.ComponentClassification.BlockReversedMutualEven

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OddBlockSylowAbelian

theorem fixed_factor {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hodd : Odd (Nat.card ↥(UniversalOrbitBlock.block component)))
    (acting : Subgroup G) (htwo : IsPGroup 2 acting)
    (hnormalizes : acting ≤ UniversalOrbitBlock.normalizer component) :
    ∃ factor ∈ UniversalOrbitBlock.block component, acting ≤ Subgroup.normalizer (factor : Set G) := by
  let Index := ↥(UniversalOrbitBlock.block component)
  let action : MulAction acting Index :=
    { smul := fun actor factor => ⟨UniversalOrbitBlock.conjugate factor.val actor.val,
        (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple actor.val).mp
          (hnormalizes actor.property) factor.val factor.property⟩
      one_smul := by
        intro factor
        apply Subtype.ext
        exact UniversalOrbitBlock.conjugate_one factor.val
      mul_smul := by
        intro first second factor
        apply Subtype.ext
        exact (UniversalOrbitBlock.conjugate_conjugate factor.val second.val first.val).symm }
  let := action
  obtain ⟨factor, hfactor⟩ := htwo.nonempty_fixed_point_of_prime_not_dvd_card Index hodd.not_two_dvd_nat
  refine ⟨factor.val, factor.property, ?_⟩
  intro actor hactor
  apply (CommutingComponentFamily.normalizer_iff_conjugate_eq _ actor).mpr
  have hfixed := MulAction.mem_fixedPoints.mp hfactor (⟨actor, hactor⟩ : acting)
  exact congrArg Subtype.val hfixed

theorem sylow_in_intermediate {G : Type*} [Group G] [Finite G]
    (overgroup intermediate : Subgroup G) (hintermediate : intermediate ≤ overgroup)
    (sylow : Sylow 2 overgroup)
    (hcontained : (sylow : Subgroup overgroup).map overgroup.subtype ≤ intermediate) :
    ∃ restricted : Sylow 2 intermediate,
      (restricted : Subgroup intermediate).map intermediate.subtype = (sylow : Subgroup overgroup).map overgroup.subtype := by
  let image := (sylow : Subgroup overgroup).map overgroup.subtype
  let localSubgroup := image.subgroupOf intermediate
  have htwo : IsPGroup 2 localSubgroup := (sylow.isPGroup'.map overgroup.subtype).comap_subtype
  have hmaximal : ∀ candidate : Subgroup intermediate, IsPGroup 2 candidate → localSubgroup ≤ candidate → candidate ≤ localSubgroup := by
    intro candidate hcandidateTwo hle
    let candidateImage := candidate.map intermediate.subtype
    have hcandidateIntermediate : candidateImage ≤ intermediate := by
      rintro member ⟨lift, hlift, rfl⟩
      exact lift.property
    have hcandidateOvergroup := hcandidateIntermediate.trans hintermediate
    have hcandidateTwoImage := hcandidateTwo.map intermediate.subtype
    have himageLe : image ≤ candidateImage := by
      have hmap := Subgroup.map_mono (f := intermediate.subtype) hle
      rw [Subgroup.map_subgroupOf_eq_of_le hcontained] at hmap
      exact hmap
    have hsylowContained : (sylow : Subgroup overgroup) ≤ candidateImage.subgroupOf overgroup := by
      intro member hmember
      exact himageLe (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)
    have heq := sylow.is_maximal' (hcandidateTwoImage.comap_subtype (K := overgroup)) hsylowContained
    intro member hmember
    have hlocal : (⟨member.val, hcandidateOvergroup (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)⟩ : overgroup) ∈
        (sylow : Subgroup overgroup) := by
      rw [← heq]
      exact Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨member.val, hcandidateOvergroup (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)⟩, hlocal, rfl⟩
  let restricted : Sylow 2 intermediate := ⟨localSubgroup, htwo,
    fun {candidate} hcandidate hle => le_antisymm (hmaximal candidate hcandidate hle) hle⟩
  exact ⟨restricted, Subgroup.map_subgroupOf_eq_of_le hcontained⟩

theorem forward {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hodd : Odd (Nat.card ↥(UniversalOrbitBlock.block component)))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (hmutualEven : ∀ first ∈ UniversalOrbitBlock.block component, ∀ second ∈ UniversalOrbitBlock.block component,
      Even (Nat.card ↥(first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G))) ∧
        Even (Nat.card ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G))))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (sylow : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) :
    IsMulCommutative (sylow : Subgroup ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) := by
  classical
  let overlap := first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let image := (sylow : Subgroup overlap).map overlap.subtype
  let conjugate := UniversalOrbitBlock.conjugate component actor
  have himageOverlap : image ≤ overlap := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenConjugate := UniversalOrbitBlock.orbit_even component heven _ horbit
  have huniversalConjugate := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  have hquasisimpleConjugate := UniversalOrbitBlock.orbit_quasisimple component hquasisimple _ horbit
  have hoddConjugate : Odd (Nat.card ↥(UniversalOrbitBlock.block conjugate)) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hodd
  have himageNormalizer : image ≤ UniversalOrbitBlock.normalizer conjugate := by
    rw [← OrbitBlockConjugation.normalizer]
    exact himageOverlap.trans inf_le_right
  obtain ⟨factor, hfactor, hnormalizes⟩ := fixed_factor conjugate hevenConjugate huniversalConjugate hquasisimpleConjugate
    hoddConjugate image (sylow.isPGroup'.map overlap.subtype) himageNormalizer
  let original := UniversalOrbitBlock.conjugate factor actor⁻¹
  have horiginal : original ∈ UniversalOrbitBlock.block component := by
    have hback := (OrbitBlockConjugation.block conjugate factor actor⁻¹).mpr hfactor
    change original ∈ UniversalOrbitBlock.block
      (UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate component actor) actor⁻¹) at hback
    rwa [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hback
  have hrestore : UniversalOrbitBlock.conjugate original actor = factor := by
    change UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate factor actor⁻¹) actor = factor
    rw [UniversalOrbitBlock.conjugate_conjugate, mul_inv_cancel, UniversalOrbitBlock.conjugate_one]
  let mutualNormalizer := first ⊓ Subgroup.normalizer (factor : Set G)
  have hmutualOverlap : mutualNormalizer ≤ overlap := by
    change first ⊓ Subgroup.normalizer (factor : Set G) ≤ first ⊓ _
    apply inf_le_inf_left
    rw [← hrestore]
    exact BlockMutualRanks.image_factor_normalizer_le component heven huniversal hquasisimple original horiginal actor
  obtain ⟨restricted, hrestricted⟩ := sylow_in_intermediate overlap mutualNormalizer hmutualOverlap sylow
    (le_inf (himageOverlap.trans inf_le_left) hnormalizes)
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨other, hother, _⟩ := ComponentFamilyPumpUpFusion.exists_outside_two hfamilyCard
    (⟨first, hfirst⟩ : Index) (⟨first, hfirst⟩ : Index)
  let otherMutual := other.val ⊓ Subgroup.normalizer (factor : Set G)
  let otherSylow : Sylow 2 otherMutual := Classical.choice inferInstance
  have hconjugateCard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block conjugate) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have hpair := BlockPairSylowOmega.pair conjugate hevenConjugate huniversalConjugate hquasisimpleConjugate hconjugateCard
    (BlockExternalControlConjugation.control component actor hcontrol) actor⁻¹
      (OrbitBlockConjugation.inverse_outside component actor hactor) (BlockReversedMutualEven.even component actor hmutualEven)
        factor (UniversalOrbitBlock.conjugate first actor) (UniversalOrbitBlock.conjugate other.val actor) hfactor
          ((OrbitBlockConjugation.block component first actor).mpr hfirst)
          ((OrbitBlockConjugation.block component other.val actor).mpr other.property)
          (by
            intro heq
            have hinj := Subgroup.map_injective (MulAut.conj actor).injective heq
            exact hother (Subtype.ext hinj.symm))
  have hfirstBack : UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate first actor) actor⁻¹ = first := by
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one]
  have hotherBack : UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate other.val actor) actor⁻¹ = other.val := by
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one]
  rw [hfirstBack, hotherBack] at hpair
  have habJoin := (hpair restricted otherSylow).1
  have habImage := BlockPairSylowOmega.abelian_of_le le_sup_left habJoin
  rw [hrestricted] at habImage
  apply isMulCommutative_iff.mpr
  intro left right
  apply Subtype.ext
  apply Subtype.ext
  change left.val.val * right.val.val = right.val.val * left.val.val
  have hleft : left.val.val ∈ image := Subgroup.mem_map.mpr ⟨left.val, left.property, rfl⟩
  have hright : right.val.val ∈ image := Subgroup.mem_map.mpr ⟨right.val, right.property, rfl⟩
  exact congrArg Subtype.val (isMulCommutative_iff.mp habImage
    (⟨left.val.val, hleft⟩ : image) (⟨right.val.val, hright⟩ : image))

theorem reverse {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hodd : Odd (Nat.card ↥(UniversalOrbitBlock.block component)))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (hmutualEven : ∀ first ∈ UniversalOrbitBlock.block component, ∀ second ∈ UniversalOrbitBlock.block component,
      Even (Nat.card ↥(first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G))) ∧
        Even (Nat.card ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G))))
    (second : Subgroup G) (hsecond : second ∈ UniversalOrbitBlock.block component)
    (sylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component)) :
    IsMulCommutative (sylow : Subgroup ↥(UniversalOrbitBlock.conjugate second actor ⊓ UniversalOrbitBlock.normalizer component)) := by
  let conjugate := UniversalOrbitBlock.conjugate component actor
  have horbit := UniversalOrbitBlock.orbit_conjugate component component (UniversalOrbitBlock.mem_orbit_self component) actor
  have hevenConjugate := UniversalOrbitBlock.orbit_even component heven _ horbit
  have huniversalConjugate := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  have hquasisimpleConjugate := UniversalOrbitBlock.orbit_quasisimple component hquasisimple _ horbit
  have hcardConjugate : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block conjugate) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have hoddConjugate : Odd (Nat.card ↥(UniversalOrbitBlock.block conjugate)) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hodd
  have hab := forward conjugate hevenConjugate huniversalConjugate hquasisimpleConjugate hcardConjugate hoddConjugate
    (BlockExternalControlConjugation.control component actor hcontrol) actor⁻¹
      (OrbitBlockConjugation.inverse_outside component actor hactor)
      (BlockReversedMutualEven.even component actor hmutualEven) (UniversalOrbitBlock.conjugate second actor)
        ((OrbitBlockConjugation.block component second actor).mpr hsecond)
  rw [OrbitBlockConjugation.normalizer_back] at hab
  exact hab sylow

end CFSG.ComponentClassification.OddBlockSylowAbelian
