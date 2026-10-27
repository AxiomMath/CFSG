module

public import CFSG.CharacterTheory.Semidihedral.Principal.DefectNormalizerPreimage
public import CFSG.CharacterTheory.TwoRankLowerBound.LocalBlockExistence

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem classDefect_of_subgroupsConjugate (p : ℕ) [Fact p.Prime] {Z : ConjClasses G}
    {Q Q' : Subgroup G} (hZ : classDefect p Z Q) (hconj : subgroupsConjugate Q Q') :
    classDefect p Z Q' := by
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨r, hr, hat⟩ := (classDefect_iff_exists_at p Z Q).mp hZ
  have htransported := classDefectAt_conjugation p hat g
  rw [hg] at htransported
  exact (classDefect_iff_exists_at p Z Q').mpr
    ⟨g * r * g⁻¹, by rw [conjugacyClass_mk_conjugation, hr], htransported⟩

theorem brauerProjection_conjugacyClassSum_eq_zero (ring : Subring ℂ) (D : Subgroup G)
    (Y : ConjClasses G)
    (hnone : ¬ ∃ y : G, ConjClasses.mk y = Y ∧ y ∈ Subgroup.centralizer (D : Set G)) :
    centralNormalizerCoefficientProjection ring D (Subgroup.normalizer (D : Set G))
        (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl (centralConjugacyClassSum ring Y) =
      0 := by
  apply Subtype.ext
  ext element
  rw [centralNormalizerCoefficientProjection_coeff]
  change (if element.val ∈ Subgroup.centralizer (D : Set G) then
    (conjugacyClassSum (ring := ℂ) Y).coeff element.val else 0) = 0
  rw [conjugacyClassSum_coeff]
  by_cases hcentralizes : element.val ∈ Subgroup.centralizer (D : Set G)
  · rw [ite_eq_left hcentralizes,
      ite_eq_right fun hmember => hnone ⟨element.val, hmember, hcentralizes⟩]
  · rw [ite_eq_right hcentralizes]

theorem defect_normalizer_brauer_image_defect (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (D : Subgroup G) (hD : IsPGroup p D)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (D : Set G)))
    {θ : localBasis.index} {χ : basis.index}
    (hθ : coefficientBlockDefect localBasis ideal p θ
      (D.subgroupOf (Subgroup.normalizer (D : Set G))))
    (hχ : brauerNormalizerCharacterResidueHom ideal p D hD (Subgroup.normalizer (D : Set G))
      (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl localBasis θ =
        centralCharacterResidueHom basis ideal χ) :
    coefficientBlockDefect basis ideal p χ D := by
  have hvalue : ∀ Y : ConjClasses G, centralCharacterResidueHom basis ideal χ
      (centralConjugacyClassSum _ Y) = centralCharacterResidueHom localBasis ideal θ
        (centralNormalizerCoefficientProjection (localizedComplexIntegerRing ideal) D
          (Subgroup.normalizer (D : Set G)) (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl
          (centralConjugacyClassSum _ Y)) := fun Y => by
    rw [← hχ]
    rfl
  refine ⟨?_, fun Y U hYU hY => ?_⟩
  · obtain ⟨L, hL, hLres⟩ := hθ.1
    obtain ⟨x, hxL, hx⟩ := classDefect_normalizer_lift p D L hL
    refine ⟨ConjClasses.mk x.val, classDefectAt_classDefect hx, ?_⟩
    rw [hvalue, CFSG.Semidihedral.Principal.centralNormalizerCoefficientProjection_conjugacyClassSum
      _ p D x hx, hxL]
    exact hLres
  · apply (class_meets_centralizer_iff_subconjugate p D hD hYU).mp
    by_contra hnone
    apply hY
    rw [hvalue, brauerProjection_conjugacyClassSum_eq_zero _ D Y hnone, map_zero]

theorem defect_normalizer_brauer_injective (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (D : Subgroup G) (hD : IsPGroup p D)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (D : Set G)))
    {θ₁ θ₂ : localBasis.index}
    (h₁ : coefficientBlockDefect localBasis ideal p θ₁
      (D.subgroupOf (Subgroup.normalizer (D : Set G))))
    (h₂ : coefficientBlockDefect localBasis ideal p θ₂
      (D.subgroupOf (Subgroup.normalizer (D : Set G))))
    (hBr : brauerNormalizerCharacterResidueHom ideal p D hD (Subgroup.normalizer (D : Set G))
        (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl localBasis θ₁ =
      brauerNormalizerCharacterResidueHom ideal p D hD (Subgroup.normalizer (D : Set G))
        (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl localBasis θ₂) :
    sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₁ θ₂ := by
  let : Field (ComplexAlgebraicIntegers ⧸ ideal) := Ideal.Quotient.field ideal
  let : Fintype (ConjClasses (Subgroup.normalizer (D : Set G))) := Fintype.ofFinite _
  have hagree : ∀ L : ConjClasses (Subgroup.normalizer (D : Set G)),
      classDefect p L (D.subgroupOf (Subgroup.normalizer (D : Set G))) →
      centralCharacterResidueHom localBasis ideal θ₁ (centralConjugacyClassSum _ L) =
        centralCharacterResidueHom localBasis ideal θ₂ (centralConjugacyClassSum _ L) := by
    intro L hL
    obtain ⟨x, hxL, hx⟩ := classDefect_normalizer_lift p D L hL
    have e := congrArg (fun f => f (centralConjugacyClassSum (localizedComplexIntegerRing ideal)
      (ConjClasses.mk x.val))) hBr
    change centralCharacterResidueHom localBasis ideal θ₁
        (centralNormalizerCoefficientProjection _ D (Subgroup.normalizer (D : Set G))
          (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl _) =
      centralCharacterResidueHom localBasis ideal θ₂
        (centralNormalizerCoefficientProjection _ D (Subgroup.normalizer (D : Set G))
          (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl _) at e
    rw [CFSG.Semidihedral.Principal.centralNormalizerCoefficientProjection_conjugacyClassSum _ p D x
      hx, hxL] at e
    exact e
  obtain ⟨L₀, hL₀, hc⟩ := h₁.1
  rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
  apply centralCharacterResidueHom_eq_of_class_values
  intro Y
  apply mul_left_cancel₀ hc
  rw [centralCharacterResidueHom_class_product, hagree L₀ hL₀,
    centralCharacterResidueHom_class_product]
  refine Finset.sum_congr rfl fun Z _ => ?_
  by_cases hn : p ∣ classProductCoefficient L₀ Y (conjugacyClassRepresentative Z)
  · rw [(CharP.cast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) p _).mpr hn, zero_mul, zero_mul]
  · by_cases hzero :
        centralCharacterResidueHom localBasis ideal θ₁ (centralConjugacyClassSum _ Z) = 0 ∧
        centralCharacterResidueHom localBasis ideal θ₂ (centralConjugacyClassSum _ Z) = 0
    · rw [hzero.1, hzero.2]
    · obtain ⟨QZ, hQZ⟩ := classDefect_exists p Z
      obtain ⟨QY, hQY⟩ := classDefect_exists p Y
      have hcontain := (classProduct_defect_containment p L₀ Y Z (conjugacyClassRepresentative Z)
        (conjugacyClassRepresentative_spec Z) hn hQZ hL₀ hQY).1
      have hlower : subgroupSubconjugate (D.subgroupOf (Subgroup.normalizer (D : Set G))) QZ := by
        by_cases hfirst : centralCharacterResidueHom localBasis ideal θ₁
            (centralConjugacyClassSum _ Z) = 0
        · have hsecond : centralCharacterResidueHom localBasis ideal θ₂
              (centralConjugacyClassSum _ Z) ≠ 0 := fun h => hzero ⟨hfirst, h⟩
          exact h₂.2 Z QZ hQZ hsecond
        · exact h₁.2 Z QZ hQZ hfirst
      have hZ : classDefect p Z (D.subgroupOf (Subgroup.normalizer (D : Set G))) :=
        classDefect_of_subgroupsConjugate p hQZ
        (subgroupSubconjugate_antisymm hcontain hlower)
      rw [hagree Z hZ]

theorem defect_normalizer_brauer_correspondence (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (D : Subgroup G) (hD : IsPGroup p D)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (D : Set G))) :
    (∀ θ : localBasis.index, ∃ χ : basis.index,
      brauerNormalizerCharacterResidueHom ideal p D hD (Subgroup.normalizer (D : Set G))
        (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl localBasis θ =
          centralCharacterResidueHom basis ideal χ) ∧
    (∀ (θ : localBasis.index) (χ : basis.index),
      coefficientBlockDefect localBasis ideal p θ (D.subgroupOf (Subgroup.normalizer (D : Set G))) →
      brauerNormalizerCharacterResidueHom ideal p D hD (Subgroup.normalizer (D : Set G))
        (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl localBasis θ =
          centralCharacterResidueHom basis ideal χ →
      coefficientBlockDefect basis ideal p χ D) ∧
    (∀ χ : basis.index, coefficientBlockDefect basis ideal p χ D →
      ∃ θ : localBasis.index,
        coefficientBlockDefect localBasis ideal p θ
          (D.subgroupOf (Subgroup.normalizer (D : Set G))) ∧
        brauerNormalizerCharacterResidueHom ideal p D hD (Subgroup.normalizer (D : Set G))
          (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl localBasis θ =
            centralCharacterResidueHom basis ideal χ) ∧
    (∀ θ₁ θ₂ : localBasis.index,
      coefficientBlockDefect localBasis ideal p θ₁
        (D.subgroupOf (Subgroup.normalizer (D : Set G))) →
      coefficientBlockDefect localBasis ideal p θ₂
        (D.subgroupOf (Subgroup.normalizer (D : Set G))) →
      brauerNormalizerCharacterResidueHom ideal p D hD (Subgroup.normalizer (D : Set G))
          (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl localBasis θ₁ =
        brauerNormalizerCharacterResidueHom ideal p D hD (Subgroup.normalizer (D : Set G))
          (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl localBasis θ₂ →
      sameCoefficientBlock localBasis (localizedComplexIntegerRing ideal) θ₁ θ₂) := by
  refine ⟨fun θ => brauerNormalizer_block_image_exists basis ideal p D hD _
      (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl localBasis θ,
    fun θ χ hθ hχ => defect_normalizer_brauer_image_defect basis ideal p D hD localBasis hθ hχ,
    fun χ hχ => ?_,
    fun θ₁ θ₂ h₁ h₂ hBr => defect_normalizer_brauer_injective ideal p D hD localBasis h₁ h₂ hBr⟩
  obtain ⟨θ, hθ⟩ := brauerNormalizer_local_block_exists_of_subconjugate basis ideal p D hD
    (Subgroup.normalizer (D : Set G)) (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl
    localBasis hχ (subgroupSubconjugate_refl D)
  exact ⟨θ, CFSG.Semidihedral.Principal.defect_normalizer_brauer_preimage_exact_defect basis ideal p
    D hD χ hχ localBasis θ hθ, hθ⟩

end CFSG.Wreathed
