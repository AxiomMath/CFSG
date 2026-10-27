module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.EqualDefectPrincipal
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalBlockExistence
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerReduction
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalImage

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem subgroupOf_map_subtype_self {G : Type*} [Group G]
    (overgroup : Subgroup G) (subgroup : Subgroup overgroup) :
    (subgroup.map overgroup.subtype).subgroupOf overgroup = subgroup := by
  ext element
  change element.val ∈ subgroup.map overgroup.subtype ↔ element ∈ subgroup
  constructor
  · intro hmember
    obtain ⟨factor, hfactor, hequal⟩ := Subgroup.mem_map.mp hmember
    have hequal' : factor = element := Subtype.ext hequal
    exact hequal' ▸ hfactor
  · intro hmember
    exact Subgroup.mem_map.mpr ⟨element, hmember, rfl⟩

theorem normalizer_counterexample_larger
    (prime : ℕ) (hprime : prime.Prime) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (hprimeMem : (prime : BlocksAlgInt) ∈ m) (G : Type) [Group G] [Finite G]
    (subgroup : Subgroup G) (hpGroup : IsPGroup prime subgroup)
    {block : Set (Subgroup.normalizer (subgroup : Set G) → ℂ)}
    (hblock : BlocksIsBlock m (Subgroup.normalizer (subgroup : Set G)) block)
    (hnotPrincipal : block ≠ BlocksPrincipalBlock m (Subgroup.normalizer (subgroup : Set G)))
    (hcorrespondence : BlocksBrauerCorr m subgroup (Subgroup.normalizer (subgroup : Set G))
      block (BlocksPrincipalBlock m G)) :
    ∃ larger overgroup : Subgroup G, IsPGroup prime larger ∧
      Nat.card subgroup < Nat.card larger ∧ larger ≤ overgroup ∧
      Subgroup.centralizer (larger : Set G) ≤ overgroup ∧
      overgroup ≤ Subgroup.normalizer (larger : Set G) ∧
      ∃ localBlock : Set (overgroup → ℂ), BlocksIsBlock m overgroup localBlock ∧
        localBlock ≠ BlocksPrincipalBlock m overgroup ∧
        BlocksBrauerCorr m larger overgroup localBlock (BlocksPrincipalBlock m G) := by
  classical
  let normalizer := Subgroup.normalizer (subgroup : Set G)
  let localSubgroup := subgroup.subgroupOf normalizer
  have hsubgroup : subgroup ≤ normalizer := Subgroup.le_normalizer
  let : localSubgroup.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (le_refl normalizer)
  have hpLocal := hpGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hsubgroup).symm
  obtain ⟨character, hcharacter⟩ := block_nonempty m hblock
  have hcharacterIrr := block_subset_irr m hblock hcharacter
  obtain ⟨defect, hdefect⟩ := blockDefect_exists prime hprime m hm hprimeMem normalizer hcharacterIrr
  have hlocalLe := normalPSubgroup_le_blockDefect prime hprime m hm hprimeMem normalizer
    localSubgroup hpLocal hcharacterIrr hdefect
  have hdefectNe : defect ≠ localSubgroup := by
    intro hequal
    rw [hequal] at hdefect
    exact hnotPrincipal (normalizer_equal_defect_principal prime hprime m hm hprimeMem G
      subgroup hpGroup hblock hcharacter hdefect hcorrespondence)
  let larger := defect.map normalizer.subtype
  have hlargerNormalizer : larger ≤ normalizer := Subgroup.map_subtype_le _
  have hsubgroupLarger : subgroup ≤ larger := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hsubgroup]
    exact Subgroup.map_mono hlocalLe
  have hcardLocal : Nat.card localSubgroup < Nat.card defect := by
    have hle := Subgroup.card_le_of_le hlocalLe
    have hne : Nat.card localSubgroup ≠ Nat.card defect := by
      intro hequal
      exact hdefectNe (Subgroup.eq_of_le_of_card_ge hlocalLe hequal.ge).symm
    omega
  have hcard : Nat.card subgroup < Nat.card larger := by
    have hfirst := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsubgroup).toEquiv
    have hsecond := Nat.card_congr (defect.equivMapOfInjective normalizer.subtype
      normalizer.subtype_injective).toEquiv
    exact hfirst ▸ hsecond ▸ hcardLocal
  have hpLarger : IsPGroup prime larger := (classDefect_isPGroup prime hdefect.1.choose_spec.1).map _
  let overgroup := larger ⊔ Subgroup.centralizer (larger : Set G)
  have hlargerOvergroup : larger ≤ overgroup := le_sup_left
  have hcentralizer : Subgroup.centralizer (larger : Set G) ≤ overgroup := le_sup_right
  have hovergroupNormalizer : overgroup ≤ Subgroup.normalizer (larger : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hovergroupSmallNormalizer : overgroup ≤ normalizer :=
    sup_le hlargerNormalizer ((Subgroup.centralizer_le hsubgroupLarger).trans
      (Subgroup.centralizer_le_normalizer _))
  let localOvergroup := overgroup.subgroupOf normalizer
  have hdefectOvergroup : defect ≤ localOvergroup := by
    intro member hmember
    exact hlargerOvergroup (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)
  have hcentralizerLocal : Subgroup.centralizer (defect : Set normalizer) ≤ localOvergroup := by
    intro member hmember
    apply hcentralizer
    apply Subgroup.mem_centralizer_iff.mpr
    intro factor hfactor
    obtain ⟨localFactor, hlocalFactor, rfl⟩ := Subgroup.mem_map.mp hfactor
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hmember localFactor hlocalFactor)
  have hnormalizerLocal : localOvergroup ≤ Subgroup.normalizer (defect : Set normalizer) := by
    intro member hmember
    apply Subgroup.mem_normalizer_iff.mpr
    intro factor
    have hequivalence : ∀ element : normalizer, element ∈ defect ↔ element.val ∈ larger := by
      intro element
      change element ∈ defect ↔ element ∈ larger.subgroupOf normalizer
      rw [subgroupOf_map_subtype_self]
    rw [hequivalence, hequivalence]
    exact Subgroup.mem_normalizer_iff.mp (hovergroupNormalizer hmember) factor.val
  obtain ⟨localBlock, hlocalBlock, hlocalCorr⟩ := localBlock_exists_of_subconjugate_defect
    m hm prime hprime hprimeMem normalizer defect localOvergroup
    (classDefect_isPGroup prime hdefect.1.choose_spec.1) hcentralizerLocal hnormalizerLocal
    hblock hcharacter hdefect (subgroupSubconjugate_refl defect)
  have hlocalNotPrincipal : localBlock ≠ BlocksPrincipalBlock m localOvergroup := by
    intro hequal
    have hprincipalCorr := brauerCorr_principal m hm prime hprime hprimeMem normalizer defect localOvergroup
      (classDefect_isPGroup prime hdefect.1.choose_spec.1) hcentralizerLocal hnormalizerLocal
    rw [← hequal] at hprincipalCorr
    exact hnotPrincipal (brauerCorr_unique_image m hm normalizer defect localOvergroup
      (block_nonempty m hlocalBlock) hblock (principal_isBlock m normalizer) hlocalCorr hprincipalCorr)
  obtain ⟨localCharacter, hlocalCharacter⟩ := block_nonempty m hlocalBlock
  have hlocalIrr := block_subset_irr m hlocalBlock hlocalCharacter
  let equivalence := Subgroup.subgroupOfEquivOfLe hovergroupSmallNormalizer
  let transferred := localCharacter ∘ equivalence.symm
  have htransferredIrr : transferred ∈ BlocksIrr overgroup := irr_comp_equiv equivalence.symm hlocalIrr
  let transferredBlock := BlocksBlockOf m overgroup transferred
  have htransferredBlock : BlocksIsBlock m overgroup transferredBlock := ⟨transferred, htransferredIrr, rfl⟩
  have htransferredMember : transferred ∈ transferredBlock := mem_blockOf_self m htransferredIrr
  have htransferredNotPrincipal : transferredBlock ≠ BlocksPrincipalBlock m overgroup := by
    intro hequal
    have hprincipalTransferred : transferred ∈ BlocksPrincipalBlock m overgroup := hequal ▸ htransferredMember
    have hprincipalLocal := principal_comp_equiv m hm equivalence hprincipalTransferred
    have hcharacterEq : transferred ∘ equivalence = localCharacter := by
      ext element
      exact congrArg localCharacter (equivalence.symm_apply_apply element)
    rw [hcharacterEq] at hprincipalLocal
    exact hlocalNotPrincipal (blocks_eq_of_common_member m hlocalBlock (principal_isBlock m localOvergroup)
      hlocalCharacter hprincipalLocal)
  refine ⟨larger, overgroup, hpLarger, hcard, hlargerOvergroup, hcentralizer,
    hovergroupNormalizer, transferredBlock, htransferredBlock, htransferredNotPrincipal, ?_⟩
  apply brauerCorr_of_trivial_scalar m hm G larger overgroup htransferredBlock htransferredMember
    hovergroupNormalizer
  intro coefficients hcoefficients
  have hprojected := brauerProj_central m hm subgroup normalizer (le_refl normalizer) hcoefficients
  have hfirst := hcorrespondence coefficients hcoefficients (fun _ => 1) (trivial_mem_principal m G)
    character hcharacter
  have hsecond := hlocalCorr (BlocksBrauerProj subgroup normalizer coefficients) hprojected
    character hcharacter localCharacter hlocalCharacter
  have hprojection :
      BlocksBrauerProj defect localOvergroup (BlocksBrauerProj subgroup normalizer coefficients) =
        BlocksBrauerProj larger overgroup coefficients ∘ equivalence := by
    ext element
    have hequal := brauerProj_transitive subgroup larger normalizer overgroup hsubgroupLarger
      hlargerNormalizer hovergroupSmallNormalizer coefficients (equivalence element)
    have hdefectEq : larger.subgroupOf normalizer = defect := subgroupOf_map_subtype_self normalizer defect
    rw [hdefectEq] at hequal
    exact hequal
  rw [hprojection] at hsecond
  have hscalar := centralChar_comp_equiv equivalence transferred (BlocksBrauerProj larger overgroup coefficients)
  have hcharacterEq : transferred ∘ equivalence = localCharacter := by
    ext element
    exact congrArg localCharacter (equivalence.symm_apply_apply element)
  rw [hcharacterEq] at hscalar
  rw [hscalar] at hsecond
  exact localMaxIdeal_trans m hm hfirst hsecond

end CFSG.BrauerThirdMainTheorem.Helpers
