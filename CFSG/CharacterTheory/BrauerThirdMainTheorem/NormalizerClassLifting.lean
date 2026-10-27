module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.DefectMaximality
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Projection
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalBlockDefects

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem normalizer_classDefect_lifts {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G)
    (hpGroup : IsPGroup prime subgroup)
    (element : Subgroup.normalizer (subgroup : Set G))
    (hdefect : classDefect prime (ConjClasses.mk element)
      (subgroup.subgroupOf (Subgroup.normalizer (subgroup : Set G)))) :
    classDefect prime (ConjClasses.mk element.val) subgroup := by
  let normalizer := Subgroup.normalizer (subgroup : Set G)
  let localSubgroup := subgroup.subgroupOf normalizer
  have hsubgroup : subgroup ≤ normalizer := Subgroup.le_normalizer
  have hcentralizesLocal : localSubgroup ≤ Subgroup.centralizer {element} := by
    obtain ⟨representative, hrepresentative, hcentralizes⟩ := classDefect_centralizes prime hdefect
    let : localSubgroup.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (le_refl normalizer)
    have hrep : representative ∈ Subgroup.centralizer (localSubgroup : Set normalizer) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      exact (Subgroup.mem_centralizer_iff.mp (hcentralizes hmember)
        representative (Set.mem_singleton representative)).symm
    have helement := class_centralizer_mem_of_normal localSubgroup hrepresentative hrep
    intro member hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    obtain rfl := Set.mem_singleton_iff.mp htest
    exact (Subgroup.mem_centralizer_iff.mp helement member hmember).symm
  have hcentralizes : subgroup ≤ Subgroup.centralizer {element.val} := by
    intro member hmember
    have hlocal : (⟨member, hsubgroup hmember⟩ : normalizer) ∈ localSubgroup := hmember
    have hcommute := Subgroup.mem_centralizer_iff.mp (hcentralizesLocal hlocal)
      element (Set.mem_singleton element)
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    obtain rfl := Set.mem_singleton_iff.mp htest
    exact congrArg Subtype.val hcommute
  apply classDefect_of_maximal_centralizing prime element.val subgroup hpGroup hcentralizes
  intro other hpOther hinclusion hotherCentralizes
  let localNormalizer := Subgroup.normalizer (subgroup.subgroupOf other : Set other)
  have hnormalizerMaps : localNormalizer.map other.subtype ≤ normalizer := by
    intro member hmember
    obtain ⟨factor, hfactor, rfl⟩ := Subgroup.mem_map.mp hmember
    apply Subgroup.mem_normalizer_iff.mpr
    intro test
    constructor
    · intro htest
      exact (Subgroup.mem_normalizer_iff.mp hfactor ⟨test, hinclusion htest⟩).mp htest
    · intro htest
      have htestOther : test ∈ other := by
        have hconjugate : factor.val⁻¹ * (factor.val * test * factor.val⁻¹) * factor.val ∈ other :=
          other.mul_mem (other.mul_mem (other.inv_mem factor.property) (hinclusion htest)) factor.property
        have hequal : factor.val⁻¹ * (factor.val * test * factor.val⁻¹) * factor.val = test := by group
        rwa [hequal] at hconjugate
      exact (Subgroup.mem_normalizer_iff.mp hfactor ⟨test, htestOther⟩).mpr htest
  let localOther := (localNormalizer.map other.subtype).subgroupOf normalizer
  have hpLocalOther : IsPGroup prime localOther :=
    ((hpOther.to_subgroup localNormalizer).map other.subtype).of_equiv
      (Subgroup.subgroupOfEquivOfLe hnormalizerMaps).symm
  have hlocalInclusion : localSubgroup ≤ localOther := by
    intro member hmember
    change member.val ∈ localNormalizer.map other.subtype
    apply Subgroup.mem_map.mpr
    exact ⟨⟨member.val, hinclusion hmember⟩, Subgroup.le_normalizer hmember, rfl⟩
  have hlocalCentralizes : localOther ≤ Subgroup.centralizer {element} := by
    intro member hmember
    obtain ⟨factor, _, hfactor⟩ := Subgroup.mem_map.mp hmember
    have hcommute := Subgroup.mem_centralizer_iff.mp (hotherCentralizes factor.property)
      element.val (Set.mem_singleton element.val)
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    have htestEqual : test = element := Set.mem_singleton_iff.mp htest
    subst test
    apply Subtype.ext
    change element.val * member.val = member.val * element.val
    change factor.val = member.val at hfactor
    rw [← hfactor]
    exact hcommute
  have hequal := classDefect_maximal_centralizing prime hprime element hdefect
    hcentralizesLocal hpLocalOther hlocalInclusion hlocalCentralizes
  have hself : localNormalizer = subgroup.subgroupOf other := by
    apply Subgroup.map_injective other.subtype_injective
    have hmapped := congrArg (fun candidate : Subgroup normalizer => candidate.map normalizer.subtype) hequal
    rw [Subgroup.map_subgroupOf_eq_of_le hnormalizerMaps,
      Subgroup.map_subgroupOf_eq_of_le hsubgroup] at hmapped
    rw [Subgroup.map_subgroupOf_eq_of_le hinclusion]
    exact hmapped
  exact pGroup_eq_of_self_normalizing prime hprime other subgroup hpOther hinclusion hself

theorem exact_classDefect_normalizer_conjugacy {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G)
    {first second : G} (hclass : ConjClasses.mk first = ConjClasses.mk second)
    (hdefect : classDefect prime (ConjClasses.mk first) subgroup)
    (hfirst : first ∈ Subgroup.centralizer (subgroup : Set G))
    (hsecond : second ∈ Subgroup.centralizer (subgroup : Set G)) :
    ∃ conjugator : Subgroup.normalizer (subgroup : Set G),
      conjugator.val * first * conjugator.val⁻¹ = second := by
  obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass)
  have hpGroup := classDefect_isPGroup prime hdefect
  have hsecondCentralizes : subgroup ≤ Subgroup.centralizer {second} := by
    intro member hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    obtain rfl := Set.mem_singleton_iff.mp htest
    exact (Subgroup.mem_centralizer_iff.mp hsecond member hmember).symm
  have hpLocal : IsPGroup prime (subgroup.subgroupOf (Subgroup.centralizer {second})) :=
    hpGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hsecondCentralizes).symm
  obtain ⟨sylow, hsylow⟩ := hpLocal.exists_le_sylow
  let extension := (sylow : Subgroup (Subgroup.centralizer {second})).map
    (Subgroup.centralizer {second}).subtype
  have hsubgroupExtension : subgroup ≤ extension := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hsecondCentralizes]
    exact Subgroup.map_mono hsylow
  have hextension : extension = subgroup := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hsubgroupExtension
    exact (classDefect_card_eq prime hprime
      (by simpa only [hclass] using hdefect)
      (show classDefect prime (ConjClasses.mk second) extension from ⟨second, rfl, sylow, rfl⟩)).ge
  let conjugated := subgroup.map (MulAut.conj conjugator).toMonoidHom
  have hconjugatedCentralizes : conjugated ≤ Subgroup.centralizer {second} := by
    intro member hmember
    obtain ⟨factor, hfactor, rfl⟩ := Subgroup.mem_map.mp hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    have htestEqual : test = second := Set.mem_singleton_iff.mp htest
    subst test
    rw [← hconjugator]
    change (conjugator * first * conjugator⁻¹) * (conjugator * factor * conjugator⁻¹) =
      (conjugator * factor * conjugator⁻¹) * (conjugator * first * conjugator⁻¹)
    have hcommute := Subgroup.mem_centralizer_iff.mp hfirst factor hfactor
    calc
      _ = conjugator * (first * factor) * conjugator⁻¹ := by group
      _ = conjugator * (factor * first) * conjugator⁻¹ := by rw [hcommute]
      _ = _ := by group
  obtain ⟨adjustment, hadjustment⟩ := sylow_subconjugate_image_internal prime hprime
    (Subgroup.centralizer {second}) sylow (hpGroup.map _) hconjugatedCentralizes
  change conjugated.map (MulAut.conj adjustment.val).toMonoidHom ≤ extension at hadjustment
  rw [hextension] at hadjustment
  have hcombined : subgroup.map (MulAut.conj (adjustment.val * conjugator)).toMonoidHom ≤ subgroup := by
    intro member hmember
    obtain ⟨factor, hfactor, rfl⟩ := Subgroup.mem_map.mp hmember
    apply hadjustment
    apply Subgroup.mem_map.mpr
    refine ⟨conjugator * factor * conjugator⁻¹, Subgroup.mem_map.mpr ⟨factor, hfactor, rfl⟩, ?_⟩
    change adjustment.val * (conjugator * factor * conjugator⁻¹) * adjustment.val⁻¹ =
      (adjustment.val * conjugator) * factor * (adjustment.val * conjugator)⁻¹
    group
  have hcombinedEqual := Subgroup.eq_of_le_of_card_ge hcombined
    (Nat.card_congr ((MulAut.conj (adjustment.val * conjugator)).subgroupMap subgroup).toEquiv).le
  refine ⟨⟨adjustment.val * conjugator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcombinedEqual⟩, ?_⟩
  change (adjustment.val * conjugator) * first * (adjustment.val * conjugator)⁻¹ = second
  calc
    _ = adjustment.val * (conjugator * first * conjugator⁻¹) * adjustment.val⁻¹ := by group
    _ = adjustment.val * second * adjustment.val⁻¹ := by rw [hconjugator]
    _ = second := by
      rw [← Subgroup.mem_centralizer_iff.mp adjustment.property second (Set.mem_singleton second),
        mul_inv_cancel_right]

theorem normal_classDefect_centralizes {G : Type*} [Group G] (prime : ℕ)
    (subgroup : Subgroup G) [subgroup.Normal] (element : G)
    (hdefect : classDefect prime (ConjClasses.mk element) subgroup) :
    element ∈ Subgroup.centralizer (subgroup : Set G) := by
  obtain ⟨representative, hrepresentative, hcentralizes⟩ := classDefect_centralizes prime hdefect
  apply class_centralizer_mem_of_normal subgroup hrepresentative
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  exact (Subgroup.mem_centralizer_iff.mp (hcentralizes hmember)
    representative (Set.mem_singleton representative)).symm

theorem normalizer_exact_class_projection {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G)
    (hpGroup : IsPGroup prime subgroup)
    (element : Subgroup.normalizer (subgroup : Set G))
    (hdefect : classDefect prime (ConjClasses.mk element)
      (subgroup.subgroupOf (Subgroup.normalizer (subgroup : Set G)))) :
    BlocksBrauerProj subgroup (Subgroup.normalizer (subgroup : Set G))
      (classCoefficients (ConjClasses.mk element.val)) = classCoefficients (ConjClasses.mk element) := by
  classical
  let normalizer := Subgroup.normalizer (subgroup : Set G)
  let localSubgroup := subgroup.subgroupOf normalizer
  let : localSubgroup.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (le_refl normalizer)
  have hcentralizesLocal := normal_classDefect_centralizes prime localSubgroup element hdefect
  have hcentralizes : element.val ∈ Subgroup.centralizer (subgroup : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hcentralizesLocal
      ⟨member, Subgroup.le_normalizer hmember⟩ hmember)
  have hambientDefect := normalizer_classDefect_lifts prime hprime subgroup hpGroup element hdefect
  ext member
  rw [brauerProj_apply]
  have hequivalence : (ConjClasses.mk member.val = ConjClasses.mk element.val ∧
      member.val ∈ Subgroup.centralizer (subgroup : Set G)) ↔
      ConjClasses.mk member = ConjClasses.mk element := by
    constructor
    · rintro ⟨hclass, hmember⟩
      obtain ⟨conjugator, hconjugator⟩ := exact_classDefect_normalizer_conjugacy prime hprime
        subgroup hclass.symm hambientDefect hcentralizes hmember
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      exact (isConj_iff.mpr ⟨conjugator, Subtype.ext hconjugator⟩).symm
    · intro hclass
      obtain ⟨conjugator, hconjugator⟩ :=
        isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass.symm)
      have hval := congrArg Subtype.val hconjugator
      refine ⟨ConjClasses.mk_eq_mk_iff_isConj.mpr
        (isConj_iff.mpr ⟨conjugator.val, hval⟩).symm, ?_⟩
      rw [← hval]
      exact centralizer_conj_mem subgroup conjugator.property hcentralizes
  simp only [classCoefficients]
  by_cases hmemberClass : ConjClasses.mk member = ConjClasses.mk element
  · obtain ⟨hclass, hmemberCentralizes⟩ := hequivalence.mpr hmemberClass
    simp only [hmemberClass, hclass, hmemberCentralizes, ↓reduceIte]
  · by_cases hmemberCentralizes : member.val ∈ Subgroup.centralizer (subgroup : Set G)
    · have hnotClass : ConjClasses.mk member.val ≠ ConjClasses.mk element.val :=
        fun hclass => hmemberClass (hequivalence.mp ⟨hclass, hmemberCentralizes⟩)
      simp only [hmemberClass, hnotClass, hmemberCentralizes, ↓reduceIte]
    · simp only [hmemberClass, hmemberCentralizes, ↓reduceIte]

end CFSG.BrauerThirdMainTheorem.Helpers
