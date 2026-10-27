module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockResidues
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem centralChar_congr_of_class_congr (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G] (left right : G → ℂ)
    (hclasses : ∀ conjugacyClass : ConjClasses G,
      BlocksCentralChar left (classCoefficients conjugacyClass) -
        BlocksCentralChar right (classCoefficients conjugacyClass) ∈ BlocksLocalMaxIdeal m)
    {coefficients : G → ℂ} (hcoefficients : BlocksIsCentralR m coefficients) :
    BlocksCentralChar left coefficients - BlocksCentralChar right coefficients ∈
      BlocksLocalMaxIdeal m := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  choose representatives hrepresentatives using (fun conjugacyClass : ConjClasses G =>
    ConjClasses.exists_rep conjugacyClass)
  rw [central_class_expansion coefficients hcoefficients.2 representatives hrepresentatives,
    finsum_eq_sum_of_fintype, centralChar_sum, centralChar_sum,
    ← Finset.sum_sub_distrib]
  apply localMaxIdeal_sum m hm
  intro conjugacyClass _
  rw [centralChar_smul, centralChar_smul, ← mul_sub, mul_comm]
  exact localMaxIdeal_mul_localRing m hm (hclasses conjugacyClass) (hcoefficients.1 _)

theorem normalizer_equal_defect_principal
    (prime : ℕ) (hprime : prime.Prime) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (hprimeMem : (prime : BlocksAlgInt) ∈ m) (G : Type) [Group G] [Finite G]
    (subgroup : Subgroup G) (hpGroup : IsPGroup prime subgroup)
    {block : Set (Subgroup.normalizer (subgroup : Set G) → ℂ)}
    (hblock : BlocksIsBlock m (Subgroup.normalizer (subgroup : Set G)) block)
    {character : Subgroup.normalizer (subgroup : Set G) → ℂ}
    (hcharacter : character ∈ block)
    (hdefect : blockDefect prime m character
      (subgroup.subgroupOf (Subgroup.normalizer (subgroup : Set G))))
    (hcorrespondence : BlocksBrauerCorr m subgroup (Subgroup.normalizer (subgroup : Set G))
      block (BlocksPrincipalBlock m G)) :
    block = BlocksPrincipalBlock m (Subgroup.normalizer (subgroup : Set G)) := by
  classical
  let normalizer := Subgroup.normalizer (subgroup : Set G)
  let localSubgroup := subgroup.subgroupOf normalizer
  let : localSubgroup.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (le_refl normalizer)
  obtain ⟨conjugacyClass, hclassDefect, hnonzero⟩ := hdefect.1
  obtain ⟨element, helement⟩ := ConjClasses.exists_rep conjugacyClass
  have hclassElementDefect : classDefect prime (ConjClasses.mk element) localSubgroup :=
    helement ▸ hclassDefect
  have hambientDefect := normalizer_classDefect_lifts prime hprime subgroup hpGroup element hclassElementDefect
  have hprojection := normalizer_exact_class_projection prime hprime subgroup hpGroup element hclassElementDefect
  have hcongr := hcorrespondence (classCoefficients (ConjClasses.mk element.val))
    (classCoefficients_central m hm _) (fun _ => 1) (trivial_mem_principal m G) character hcharacter
  rw [hprojection, helement] at hcongr
  have hprincipalNonzero : BlocksCentralChar (fun _ : G => 1)
      (classCoefficients (ConjClasses.mk element.val)) ∉ BlocksLocalMaxIdeal m := by
    intro hzero
    have hnegative := localMaxIdeal_sub m hm hzero hcongr
    have hscalar : BlocksCentralChar character (classCoefficients conjugacyClass) ∈
        BlocksLocalMaxIdeal m := by
      convert hnegative using 1
      ring
    exact hnonzero hscalar
  obtain ⟨sylow, hsylow⟩ := principal_class_nonzero_defect_sylow prime hprime m hm hprimeMem
    (ConjClasses.mk element.val) hprincipalNonzero hambientDefect
  have hcharacterIrr := block_subset_irr m hblock hcharacter
  have hprincipal : character ∈ BlocksPrincipalBlock m normalizer := by
    apply mem_blockOf_of_centralChar_congr m hm normalizer (trivial_mem_irr normalizer) hcharacterIrr
    intro coefficients hcoefficients
    apply centralChar_congr_of_class_congr m hm normalizer character (fun _ => 1) _ hcoefficients
    intro localClass
    obtain ⟨representative, hrepresentative⟩ := ConjClasses.exists_rep localClass
    by_cases hcentralizes : representative.val ∈ Subgroup.centralizer (subgroup : Set G)
    · have hsubgroupCentralizes : (sylow : Subgroup G) ≤ Subgroup.centralizer {representative.val} := by
        rw [hsylow]
        intro member hmember
        apply Subgroup.mem_centralizer_iff.mpr
        intro test htest
        obtain rfl := Set.mem_singleton_iff.mp htest
        exact (Subgroup.mem_centralizer_iff.mp hcentralizes member hmember).symm
      have hlocalDefect : classDefect prime (ConjClasses.mk representative) localSubgroup := by
        simpa only [hsylow] using sylow_classDefect_in_subgroup prime sylow normalizer
          (hsylow.symm ▸ Subgroup.le_normalizer) representative hsubgroupCentralizes
      have hprojected := normalizer_exact_class_projection prime hprime subgroup hpGroup representative hlocalDefect
      have hblockScalar := hcorrespondence (classCoefficients (ConjClasses.mk representative.val))
        (classCoefficients_central m hm _) (fun _ => 1) (trivial_mem_principal m G) character hcharacter
      rw [hprojected, hrepresentative] at hblockScalar
      have haugmentation := principal_augmentation_congr m hm prime hprime hprimeMem subgroup normalizer
        hpGroup (Subgroup.centralizer_le_normalizer _)
        (classCoefficients_central m hm (ConjClasses.mk representative.val))
      rw [hprojected, hrepresentative] at haugmentation
      have hcongruence := localMaxIdeal_add m hm (localMaxIdeal_neg m hblockScalar) haugmentation
      convert hcongruence using 1
      ring
    · have hpLocal := hpGroup.of_equiv (Subgroup.subgroupOfEquivOfLe (show subgroup ≤ normalizer from Subgroup.le_normalizer)).symm
      have hcharacterZero : BlocksCentralChar character (classCoefficients localClass) ∈
          BlocksLocalMaxIdeal m := by
        apply normalPSubgroup_centralChar_vanishes prime hprime m hm hprimeMem normalizer
          localSubgroup hpLocal hcharacterIrr (classCoefficients_central m hm localClass)
        intro member hmember
        have hnotClass : ConjClasses.mk member ≠ localClass := by
          intro hclass
          have hrepresentativeFixed := class_centralizer_mem_of_normal localSubgroup
            (hclass.trans hrepresentative.symm) hmember
          apply hcentralizes
          apply Subgroup.mem_centralizer_iff.mpr
          intro factor hfactor
          exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hrepresentativeFixed
            ⟨factor, Subgroup.le_normalizer hfactor⟩ hfactor)
        simp only [classCoefficients, ite_eq_right hnotClass]
      have htrivialZero : BlocksCentralChar (fun _ : normalizer => 1) (classCoefficients localClass) ∈
          BlocksLocalMaxIdeal m := by
        apply normalPSubgroup_centralChar_vanishes prime hprime m hm hprimeMem normalizer
          localSubgroup hpLocal (trivial_mem_irr normalizer) (classCoefficients_central m hm localClass)
        intro member hmember
        have hnotClass : ConjClasses.mk member ≠ localClass := by
          intro hclass
          have hrepresentativeFixed := class_centralizer_mem_of_normal localSubgroup
            (hclass.trans hrepresentative.symm) hmember
          apply hcentralizes
          apply Subgroup.mem_centralizer_iff.mpr
          intro factor hfactor
          exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hrepresentativeFixed
            ⟨factor, Subgroup.le_normalizer hfactor⟩ hfactor)
        simp only [classCoefficients, ite_eq_right hnotClass]
      exact localMaxIdeal_sub m hm hcharacterZero htrivialZero
  exact blocks_eq_of_common_member m hblock (principal_isBlock m normalizer) hcharacter hprincipal

end CFSG.BrauerThirdMainTheorem.Helpers
