module

public import CFSG.LocalAnalysis.ComponentClassification.ComponentFamilyPumpUpFusion
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockCommonInvolutionStructure

theorem centralizes_factors {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (elementary : Subgroup G) (hcontained : ∀ factor ∈ UniversalOrbitBlock.block component, elementary ≤ factor) :
    ∀ factor ∈ UniversalOrbitBlock.block component, elementary ≤ Subgroup.centralizer (factor : Set G) := by
  classical
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
  intro factor hfactor
  obtain ⟨other, hother, _⟩ := ComponentFamilyPumpUpFusion.exists_outside_two hfamilyCard
    (⟨factor, hfactor⟩ : Index) (⟨factor, hfactor⟩ : Index)
  exact (hcontained other.val other.property).trans
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (UniversalOrbitBlock.block_commutes component heven huniversal other.val other.property factor hfactor
        (fun heq => hother (Subtype.ext heq))))

theorem central_generated {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (elementary : Subgroup G) (hcontained : ∀ factor ∈ UniversalOrbitBlock.block component, elementary ≤ factor) :
    elementary ≤ (Subgroup.center (UniversalOrbitBlock.generated component)).map
      (UniversalOrbitBlock.generated component).subtype := by
  have hle : elementary ≤ UniversalOrbitBlock.generated component :=
    (hcontained component (UniversalOrbitBlock.mem_block_self component)).trans
      (CommutingComponentFamily.factor_le _ component (UniversalOrbitBlock.mem_block_self component))
  have hcentralizes : UniversalOrbitBlock.generated component ≤ Subgroup.centralizer (elementary : Set G) := by
    apply sSup_le
    intro factor hfactor
    exact Subgroup.le_centralizer_iff.mp
      (centralizes_factors component heven huniversal hcard elementary hcontained factor hfactor)
  intro member hmember
  apply Subgroup.mem_map.mpr
  refine ⟨⟨member, hle hmember⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentralizes other.property) member hmember).symm

theorem normalizes_common {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (actor : G) (elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (hcontained : ∀ factor ∈ UniversalOrbitBlock.block component,
      elementary ≤ factor ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
    (hcharacterization : ∀ factor ∈ UniversalOrbitBlock.block component, ∀ member : G,
      member ∈ factor ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ∧
        orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1) :
    UniversalOrbitBlock.normalizer component ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ≤
        Subgroup.normalizer (elementary : Set G) := by
  apply Subgroup.le_set_normalizer_iff.mpr
  intro member hmember element helement
  by_cases hone : element = 1
  · rw [hone, mul_one, mul_inv_cancel]
    exact elementary.one_mem
  · have horder : orderOf element = 2 := orderOf_eq_prime (helementary.2 element helement) hone
    have hbase := (hcontained component (UniversalOrbitBlock.mem_block_self component)) helement
    have hfactor := (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple member).mp
      hmember.1 component (UniversalOrbitBlock.mem_block_self component)
    have hconjugateFactor : member * element * member⁻¹ ∈ UniversalOrbitBlock.conjugate component member :=
      Subgroup.mem_map.mpr ⟨element, hbase.1, rfl⟩
    have hconjugateNormalizer : member * element * member⁻¹ ∈
        (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom :=
      ((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).mul_mem
        (((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).mul_mem hmember.2 hbase.2)
        (((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).inv_mem hmember.2)
    have hconjugateOrder : orderOf (member * element * member⁻¹) = 2 :=
      (orderOf_injective (MulAut.conj member).toMonoidHom (MulAut.conj member).injective element).trans horder
    exact ((hcharacterization (UniversalOrbitBlock.conjugate component member) hfactor _).mp
      ⟨⟨hconjugateFactor, hconjugateNormalizer⟩, hconjugateOrder⟩).1

theorem omega_sylow {G : Type*} [Group G] [Finite G]
    (ambient elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (hcontained : elementary ≤ ambient) (hcentral : elementary ≤ Subgroup.centralizer (ambient : Set G))
    (hcoverage : ∀ member ∈ ambient, orderOf member = 2 → member ∈ elementary)
    (sylow : Sylow 2 ambient) :
    InvolutionGeneratedSubgroup.omega ((sylow : Subgroup ambient).map ambient.subtype) = elementary := by
  have hlocalNormal : (elementary.subgroupOf ambient).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact (Subgroup.le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  let : (elementary.subgroupOf ambient).Normal := hlocalNormal
  have htwo : IsPGroup 2 elementary := by
    let : CommGroup elementary := ElementaryAbelianModule.subgroupCommGroup _ helementary.1
    have hpower : ∀ member : elementary, member ^ 2 = 1 := by
      intro member
      exact Subtype.ext (helementary.2 member.val member.property)
    let : Module (ZMod 2) (Additive elementary) := ElementaryAbelianModule.moduleStructure 2 hpower
    exact IsPGroup.of_card (ElementaryAbelianModule.card_eq_pow_finrank (G := elementary) 2)
  have hlocalTwo : IsPGroup 2 (elementary.subgroupOf ambient) := htwo.comap_subtype
  have hlocalLe := hlocalTwo.le_sylow_of_normal sylow
  have helementarySylow : elementary ≤ (sylow : Subgroup ambient).map ambient.subtype := by
    intro member hmember
    exact Subgroup.mem_map.mpr ⟨⟨member, hcontained hmember⟩, hlocalLe hmember, rfl⟩
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro member hmember
    by_cases hone : member = 1
    · rw [hone]
      exact elementary.one_mem
    · obtain ⟨preimage, hpreimage, heq⟩ := Subgroup.mem_map.mp hmember.1
      exact hcoverage member (heq ▸ preimage.property) (orderOf_eq_prime hmember.2 hone)
  · intro member hmember
    exact Subgroup.subset_closure ⟨helementarySylow hmember, helementary.2 member hmember⟩

end CFSG.ComponentClassification.BlockCommonInvolutionStructure
