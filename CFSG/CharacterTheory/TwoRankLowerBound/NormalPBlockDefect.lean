module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralNormalizerProjection
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPCentralResidueVanishing
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockDefectExistence

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

theorem class_meets_centralizer_iff_subconjugate {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary : Subgroup group) (hprimary : IsPGroup prime primary)
    {conjugacyClass : ConjClasses group} {defect : Subgroup group}
    (hdefect : classDefect prime conjugacyClass defect) :
    (∃ element : group, ConjClasses.mk element = conjugacyClass ∧
      element ∈ Subgroup.centralizer (primary : Set group)) ↔ subgroupSubconjugate primary defect := by
  constructor
  · rintro ⟨element, hclass, hcentralizes⟩
    have hcontains : primary ≤ Subgroup.centralizer ({element} : Set group) := by
      intro member hmember
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hcentralizes member hmember)
    exact p_subgroup_subconjugate_classDefect prime primary hprimary element hcontains hclass hdefect
  · intro hsubconjugate
    obtain ⟨representative, hrepresentative, sylow, rfl⟩ := hdefect
    obtain ⟨conjugator, hcontains⟩ := hsubconjugate
    refine ⟨conjugator⁻¹ * representative * conjugator, ?_, ?_⟩
    · simpa only [inv_inv] using (conjugacyClass_mk_conjugation representative conjugator⁻¹).trans hrepresentative
    · have hcentralizer : primary ≤
          Subgroup.centralizer ({conjugator⁻¹ * representative * conjugator} : Set group) := by
        have hforward := (Subgroup.map_mono (hcontains.trans (sylow_image_le _ sylow))
          (f := (MulAut.conj conjugator⁻¹).toMonoidHom)).trans
            (conjugation_centralizer_singleton_le representative conjugator⁻¹)
        simpa only [conjugation_subgroup_map_mul, inv_mul_cancel,
          conjugation_subgroup_map_one, inv_inv] using hforward
      apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      exact Subgroup.mem_centralizer_singleton_iff.mp (hcentralizer hmember)

theorem normal_p_class_residue_zero {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) [primary.Normal] (hprimary : IsPGroup prime primary)
    (element : group) (houtside : element ∉ Subgroup.centralizer (primary : Set group))
    (label : basis.index) :
    centralCharacterResidueHom basis ideal label (centralConjugacyClassSum _ (ConjClasses.mk element)) = 0 := by
  apply normal_p_central_residue_zero_of_outside_centralizer basis ideal prime primary hprimary _ _ label
  intro other hcentralizes
  change (conjugacyClassSum (ring := ℂ) (ConjClasses.mk element)).coeff other = 0
  rw [conjugacyClassSum_coeff]
  apply ite_eq_right
  intro hclass
  obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass)
  apply houtside
  rw [← hconjugator]
  exact (centralizer_conjugation_mem_iff primary conjugator other
    ((Subgroup.normalizer_eq_top primary) ▸ Subgroup.mem_top conjugator)).mpr hcentralizes

theorem normal_p_le_coefficientBlockDefect {group : Type*} [Group group] [Fintype group]
    (basis : FiniteIrreducibleCharacterBasis group)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (prime : ℕ) [Fact prime.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (primary : Subgroup group) [primary.Normal] (hprimary : IsPGroup prime primary)
    {label : basis.index} {defect : Subgroup group}
    (hdefect : coefficientBlockDefect basis ideal prime label defect) : primary ≤ defect := by
  obtain ⟨conjugacyClass, hclass, hvalue⟩ := hdefect.1
  obtain ⟨representative, hrepresentative, sylow, rfl⟩ := hclass
  have hcentralizes : representative ∈ Subgroup.centralizer (primary : Set group) := by
    by_contra houtside
    apply hvalue
    rw [← hrepresentative]
    exact normal_p_class_residue_zero basis ideal prime primary hprimary representative houtside label
  have hcontains : primary ≤ Subgroup.centralizer ({representative} : Set group) := by
    intro member hmember
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcentralizes member hmember)
  have hlocal := hprimary.comap_subtype.le_sylow_of_normal sylow
  intro member hmember
  exact Subgroup.mem_map.mpr ⟨⟨member, hcontains hmember⟩, hlocal hmember, rfl⟩

end CFSG.TwoRankLowerBound.Helpers
