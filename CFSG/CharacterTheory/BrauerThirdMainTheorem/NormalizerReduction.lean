module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalPrincipalCriterion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.SubgroupCoefficients
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ProjectionTransitivity

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem normalizer_le_normalizer_centralizer {G : Type*} [Group G] (subgroup : Subgroup G) :
    Subgroup.normalizer (subgroup : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (subgroup : Set G) : Set G) := by
  intro element helement
  apply Subgroup.mem_normalizer_iff.mpr
  intro factor
  exact (centralizer_conj_iff subgroup helement).symm

theorem centralizerInclusion_range {G : Type*} [Group G]
    (subgroup overgroup : Subgroup G) (hsubgroup : subgroup ≤ overgroup)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup) :
    Set.range (Subgroup.inclusion hcentralizer) =
      (Subgroup.centralizer (subgroup.subgroupOf overgroup : Set overgroup) : Set overgroup) := by
  ext element
  change element ∈ Set.range (Subgroup.inclusion hcentralizer) ↔
    element ∈ Subgroup.centralizer (subgroup.subgroupOf overgroup : Set overgroup)
  rw [centralizer_subgroupOf_iff subgroup overgroup hsubgroup]
  constructor
  · rintro ⟨factor, rfl⟩
    exact factor.property
  · intro hmember
    exact ⟨⟨element.val, hmember⟩, Subtype.ext rfl⟩

theorem centralizerInclusion_conjugation {G : Type*} [Group G]
    (subgroup overgroup : Subgroup G)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G)) :
    ∀ conjugator : overgroup,
      ∃ equivalence : Subgroup.centralizer (subgroup : Set G) ≃*
        Subgroup.centralizer (subgroup : Set G),
      ∀ element, Subgroup.inclusion hcentralizer (equivalence element) =
        conjugator * Subgroup.inclusion hcentralizer element * conjugator⁻¹ := by
  intro conjugator
  refine ⟨subgroupConjugation (Subgroup.centralizer (subgroup : Set G)) conjugator.val
    (normalizer_le_normalizer_centralizer subgroup (hnormalizer conjugator.property)), ?_⟩
  intro element
  exact Subtype.ext rfl

theorem brauerCorr_of_trivial_scalar (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] (subgroup overgroup : Subgroup G)
    {block : Set (overgroup → ℂ)} (hblock : BlocksIsBlock m overgroup block)
    {character : overgroup → ℂ} (hcharacter : character ∈ block)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    (hscalar : ∀ coefficients : G → ℂ, BlocksIsCentralR m coefficients →
      BlocksCentralChar (fun _ => 1) coefficients -
        BlocksCentralChar character (BlocksBrauerProj subgroup overgroup coefficients) ∈ BlocksLocalMaxIdeal m) :
    BlocksBrauerCorr m subgroup overgroup block (BlocksPrincipalBlock m G) := by
  intro coefficients hcoefficients left hleft right hright
  have hleftScalar := principal_centralChar_congr m hm G hleft hcoefficients
  have hrightScalar := block_centralChar_congr m hm overgroup hblock hcharacter hright
    (brauerProj_central m hm subgroup overgroup hnormalizer hcoefficients)
  have hnegative : BlocksCentralChar character (BlocksBrauerProj subgroup overgroup coefficients) -
      BlocksCentralChar right (BlocksBrauerProj subgroup overgroup coefficients) ∈ BlocksLocalMaxIdeal m := by
    convert localMaxIdeal_neg m hrightScalar using 1
    ring
  exact localMaxIdeal_trans m hm (localMaxIdeal_trans m hm hleftScalar (hscalar coefficients hcoefficients)) hnegative

theorem normalizer_counterexample_exists (prime : ℕ) (hprime : prime.Prime)
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (hprimeMem : (prime : BlocksAlgInt) ∈ m)
    (G : Type) [Group G] [Finite G] (subgroup overgroup : Subgroup G)
    (hpGroup : IsPGroup prime subgroup) (hsubgroup : subgroup ≤ overgroup)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    {block : Set (overgroup → ℂ)} (hblock : BlocksIsBlock m overgroup block)
    (hnotPrincipal : block ≠ BlocksPrincipalBlock m overgroup)
    (hcorrespondence : BlocksBrauerCorr m subgroup overgroup block (BlocksPrincipalBlock m G)) :
    ∃ normalizerBlock : Set (Subgroup.normalizer (subgroup : Set G) → ℂ),
      BlocksIsBlock m (Subgroup.normalizer (subgroup : Set G)) normalizerBlock ∧
      normalizerBlock ≠ BlocksPrincipalBlock m (Subgroup.normalizer (subgroup : Set G)) ∧
      BlocksBrauerCorr m subgroup (Subgroup.normalizer (subgroup : Set G)) normalizerBlock
        (BlocksPrincipalBlock m G) := by
  classical
  let centralizer := Subgroup.centralizer (subgroup : Set G)
  let normalizer := Subgroup.normalizer (subgroup : Set G)
  let first := Subgroup.inclusion hcentralizer
  let second := Subgroup.inclusion hnormalizer
  let full := Subgroup.inclusion (Subgroup.centralizer_le_normalizer (subgroup : Set G))
  have hcomp : second.comp first = full := rfl
  obtain ⟨character, hcharacter⟩ := block_nonempty m hblock
  let localCharacter : BlocksIrr overgroup := ⟨character, block_subset_irr m hblock hcharacter⟩
  obtain ⟨centralizerCharacter, hlocalResidue⟩ := commonCentral_residue_extension m hm centralizer overgroup
    first localCharacter
  have hle : commonCentralAlgebra m hm centralizer normalizer full ≤
      commonCentralAlgebra m hm centralizer overgroup first := by
    rw [← hcomp]
    exact commonCentral_mono m hm centralizer overgroup normalizer first second
      (Subgroup.inclusion_injective hnormalizer)
  obtain ⟨normalizerCharacter, hnormalizerResidue⟩ := commonCentral_reverse_residue_extension m hm
    centralizer normalizer full (Subgroup.inclusion_injective _) centralizerCharacter
  let : (subgroup.subgroupOf overgroup).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnormalizer
  let : (subgroup.subgroupOf normalizer).Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hlocalP := hpGroup.of_injective (Subgroup.subgroupOfEquivOfLe hsubgroup).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hsubgroup).injective
  have hnormalizerP := hpGroup.of_injective
    (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer : subgroup ≤ normalizer)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer : subgroup ≤ normalizer)).injective
  have hcentralizerNot : centralizerCharacter.val ∉ BlocksPrincipalBlock m centralizer := by
    intro hprincipal
    have hlocalPrincipal := (commonCentral_principal_iff prime hprime m hm hprimeMem centralizer overgroup
      (subgroup.subgroupOf overgroup) hlocalP first (Subgroup.inclusion_injective _)
      (centralizerInclusion_range subgroup overgroup hsubgroup hcentralizer)
      (centralizerInclusion_conjugation subgroup overgroup hcentralizer hnormalizer)
      centralizerCharacter localCharacter hlocalResidue).mpr hprincipal
    exact hnotPrincipal (block_eq_blockOf_member m hblock hcharacter |>.trans
      (blockOf_eq_of_mem m (trivial_mem_irr overgroup) hlocalPrincipal))
  have hnormalizerNot : normalizerCharacter.val ∉ BlocksPrincipalBlock m normalizer := by
    intro hprincipal
    exact hcentralizerNot ((commonCentral_principal_iff prime hprime m hm hprimeMem centralizer normalizer
      (subgroup.subgroupOf normalizer) hnormalizerP full (Subgroup.inclusion_injective _)
      (centralizerInclusion_range subgroup normalizer Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))
      (centralizerInclusion_conjugation subgroup normalizer (Subgroup.centralizer_le_normalizer _) le_rfl)
      centralizerCharacter normalizerCharacter hnormalizerResidue).mp hprincipal)
  refine ⟨BlocksBlockOf m normalizer normalizerCharacter.val,
    ⟨normalizerCharacter.val, normalizerCharacter.property, rfl⟩, ?_, ?_⟩
  · intro hequal
    exact hnormalizerNot (hequal ▸ mem_blockOf_self m normalizerCharacter.property)
  · apply brauerCorr_of_trivial_scalar m hm G subgroup normalizer
      ⟨normalizerCharacter.val, normalizerCharacter.property, rfl⟩
        (mem_blockOf_self m normalizerCharacter.property) le_rfl
    intro coefficients hcoefficients
    let : Fintype centralizer := Fintype.ofFinite _
    let normalizerCoefficients := BlocksBrauerProj subgroup normalizer coefficients
    have hnormalizerCoefficients := brauerProj_central m hm subgroup normalizer le_rfl hcoefficients
    have hprojected : (Set.range full).indicator normalizerCoefficients = normalizerCoefficients := by
      ext element
      rw [Set.indicator_apply]
      have hrange : element ∈ Set.range full ↔ element.val ∈ centralizer := by
        constructor
        · rintro ⟨factor, rfl⟩
          exact factor.property
        · intro hmember
          exact ⟨⟨element.val, hmember⟩, Subtype.ext rfl⟩
      by_cases hmember : element.val ∈ centralizer
      · rw [ite_eq_left (hrange.mpr hmember)]
      · rw [ite_eq_right (fun hmem => hmember (hrange.mp hmem))]
        exact (by
          change BlocksBrauerProj subgroup normalizer coefficients element = 0
          rw [brauerProj_apply, ite_eq_right hmember] : normalizerCoefficients element = 0).symm
    have hprojectedCentral : BlocksIsCentralR m ((Set.range full).indicator normalizerCoefficients) := by
      rw [hprojected]
      exact hnormalizerCoefficients
    let value := commonCentralRestriction m hm centralizer normalizer full
      (Subgroup.inclusion_injective _) normalizerCoefficients hnormalizerCoefficients
        hprojectedCentral
    have hvalueFull := commonCentralRestriction_inclusion m hm centralizer normalizer full
      (Subgroup.inclusion_injective _) normalizerCoefficients hnormalizerCoefficients
        hprojectedCentral
    rw [hprojected] at hvalueFull
    let localValue : commonCentralAlgebra m hm centralizer overgroup first := ⟨value.val, hle value.property⟩
    have hvalueLocal : centralLocalCoefficients m hm overgroup
        (commonCentralInclusion m hm centralizer overgroup first localValue) =
          BlocksBrauerProj subgroup overgroup coefficients := by
      ext element
      change ((MonoidAlgebra.mapDomain first value.val.val).coeff element : ℂ) = _
      rw [MonoidAlgebra.coeff_mapDomain]
      by_cases hmember : element.val ∈ centralizer
      · let factor : centralizer := ⟨element.val, hmember⟩
        have hfirst : first factor = element := Subtype.ext rfl
        rw [← hfirst, Finsupp.mapDomain_apply_of_injective (Subgroup.inclusion_injective _)]
        change centralLocalCoefficients m hm centralizer value.val factor = _
        change ((localCoefficientAlgebra m hm (normalizerCoefficients ∘ full)
          (fun factor => hnormalizerCoefficients.1 (full factor))).coeff factor : ℂ) = _
        rw [localCoefficientAlgebra_coeff]
        change BlocksBrauerProj subgroup normalizer coefficients (full factor) =
          BlocksBrauerProj subgroup overgroup coefficients (first factor)
        rw [brauerProj_apply, brauerProj_apply]
        rfl
      · have hnotRange : element ∉ Set.range first := by
          rintro ⟨factor, rfl⟩
          exact hmember factor.property
        rw [Finsupp.mapDomain_of_notMem_range _ _ hnotRange]
        rw [brauerProj_apply, ite_eq_right hmember]
        rfl
    have hequal : centralResidue m hm normalizer normalizerCharacter
        (commonCentralInclusion m hm centralizer normalizer full value) =
      centralResidue m hm overgroup localCharacter
        (commonCentralInclusion m hm centralizer overgroup first localValue) :=
      (hnormalizerResidue value).trans (hlocalResidue localValue).symm
    have hscalar := (localResidue_eq_iff m hm _ _).mp hequal
    change BlocksCentralChar normalizerCharacter.val (centralLocalCoefficients m hm normalizer
      (commonCentralInclusion m hm centralizer normalizer full value)) -
        BlocksCentralChar localCharacter.val (centralLocalCoefficients m hm overgroup
          (commonCentralInclusion m hm centralizer overgroup first localValue)) ∈ BlocksLocalMaxIdeal m at hscalar
    rw [hvalueFull, hvalueLocal] at hscalar
    have hnegative : BlocksCentralChar character (BlocksBrauerProj subgroup overgroup coefficients) -
        BlocksCentralChar normalizerCharacter.val normalizerCoefficients ∈ BlocksLocalMaxIdeal m := by
      convert localMaxIdeal_neg m hscalar using 1
      ring
    exact localMaxIdeal_trans m hm
      (hcorrespondence coefficients hcoefficients (fun _ => 1) (trivial_mem_principal m G) character hcharacter)
      hnegative

end CFSG.BrauerThirdMainTheorem.Helpers
