module

public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBrauerDefectGrowth

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem centralizer_brauer_image_defect_contains_local_defect
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (P : Subgroup G) (hP : IsPGroup p P) (D : Subgroup G) (hD : IsPGroup p D) (hPD : P ≤ D)
    (hDC : D ≤ Subgroup.centralizer (P : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set G)))
    (localLabel : localBasis.index)
    (hlocal : coefficientBlockDefect localBasis ideal p localLabel
      (D.subgroupOf (Subgroup.centralizer (P : Set G))))
    (label : basis.index)
    (hbrauer : brauerNormalizerCharacterResidueHom ideal p P hP (Subgroup.centralizer (P : Set G))
      le_rfl (Subgroup.centralizer_le_normalizer _) localBasis localLabel =
        centralCharacterResidueHom basis ideal label) :
    (∀ E : Subgroup G, coefficientBlockDefect basis ideal p label E → subgroupSubconjugate D E) ∧
      ∃ E : Subgroup G,
        coefficientBlockDefect basis ideal p label E ∧ subgroupSubconjugate D E := by
  have hsmaller : D ⊔ Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer (P : Set G) :=
    sup_le hDC (Subgroup.centralizer_le hPD)
  have hcontains : Subgroup.centralizer (D : Set G) ≤ D ⊔ Subgroup.centralizer (D : Set G) :=
    le_sup_right
  have hnormalizes : D ⊔ Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    primary_centralizer_join_le_normalizer D
  have hlocalContains := relativeCentralizer_le_join_subgroupOf D
    (Subgroup.centralizer (P : Set G)) hDC (hcontains.trans hsmaller)
  have hlocalNormalizes := relativeNormalizer_join_subgroupOf D (Subgroup.centralizer (P : Set G))
    hDC
  obtain ⟨internalBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := ↥((D ⊔ Subgroup.centralizer (D : Set G)).subgroupOf (Subgroup.centralizer (P : Set G))))
  obtain ⟨internalLabel, hinternal⟩ := brauerNormalizer_local_block_exists_of_subconjugate
    localBasis ideal p (D.subgroupOf (Subgroup.centralizer (P : Set G))) hD.comap_subtype _
    hlocalContains hlocalNormalizes internalBasis hlocal (subgroupSubconjugate_refl _)
  obtain ⟨smallerBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := ↥(D ⊔ Subgroup.centralizer (D : Set G)))
  obtain ⟨smallerLabel, htransport⟩ := centralCharacterResidueHom_transport_exists internalBasis
    smallerBasis ideal (Subgroup.subgroupOfEquivOfLe hsmaller) internalLabel
  have himage : brauerNormalizerCharacterResidueHom ideal p D hD
      (D ⊔ Subgroup.centralizer (D : Set G)) hcontains hnormalizes smallerBasis smallerLabel =
        centralCharacterResidueHom basis ideal label := by
    apply RingHom.ext
    intro value
    have htower := centralNormalizerCoefficientProjection_tower (localizedComplexIntegerRing ideal)
      P D (Subgroup.centralizer (P : Set G)) (D ⊔ Subgroup.centralizer (D : Set G)) hPD hDC
      hsmaller le_rfl (Subgroup.centralizer_le_normalizer _) hcontains hnormalizes hlocalContains
      hlocalNormalizes value
    have hvalue := htransport (centralNormalizerCoefficientProjection _
      (D.subgroupOf (Subgroup.centralizer (P : Set G)))
      ((D ⊔ Subgroup.centralizer (D : Set G)).subgroupOf (Subgroup.centralizer (P : Set G)))
      hlocalContains hlocalNormalizes
      (centralNormalizerCoefficientProjection _ P (Subgroup.centralizer (P : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) value))
    rw [htower] at hvalue
    have hlocalValue := congrArg (fun hom => hom
      (centralNormalizerCoefficientProjection _ P (Subgroup.centralizer (P : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) value)) hinternal
    have hglobalValue := congrArg (fun hom => hom value) hbrauer
    exact hvalue.trans (hlocalValue.trans hglobalValue)
  have hall : ∀ E : Subgroup G, coefficientBlockDefect basis ideal p label E →
      subgroupSubconjugate D E := fun E hE =>
    brauerNormalizer_subconjugate_of_local_block_exists basis ideal p D hD _ hcontains hnormalizes
      smallerBasis hE ⟨smallerLabel, himage⟩
  obtain ⟨E, hE⟩ := coefficientBlockDefect_exists basis ideal p label
  exact ⟨hall, E, hE, hall E hE⟩

end CFSG.Semidihedral.Principal
