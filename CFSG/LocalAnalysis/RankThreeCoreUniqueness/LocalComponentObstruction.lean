module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalElementary
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CatalogSimpleFactors
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralComponentLifts

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem catalog_non_prime_constrained_has_core_centralizer_component
    {G : Type*} [Group G] [Finite G] (hcatalog : HasCatalogSimpleSections G)
    (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := G) prime) :
    let centralizingGroup := Subgroup.centralizer
      (pCore prime (G ⧸ primeComplementCore prime) : Set (G ⧸ primeComplementCore prime))
    ∃ component : Subgroup centralizingGroup, IsComponentOf component ⊤ ∧
      prime ∣ Nat.card component ∧
      prime ∣ Nat.card (component ⧸ Subgroup.center component) ∧
      Nat.card (component ⧸ Subgroup.center component) ∈ knownSimpleOrders := by
  let centralizingGroup := Subgroup.centralizer
    (pCore prime (G ⧸ primeComplementCore prime) : Set (G ⧸ primeComplementCore prime))
  let : (pCore prime centralizingGroup).Normal := pCore_normal prime
  obtain ⟨minimalGroup, hminimal, _hperfect, _hdivides,
    simpleFactor, hfactorNormal, hfactorSimple, hfactorNonab, hfactorDivides, hfactorOrder⟩ :=
    catalog_non_prime_constrained_has_prime_divisible_simple_factor hcatalog prime hprime hconstraint
  have hcentral := pCore_centralizer_internal_pCore_le_center
    (G := G ⧸ primeComplementCore prime) prime
  have hkernel : (QuotientGroup.mk' (pCore prime centralizingGroup)).ker ≤
      Subgroup.center centralizingGroup := by
    rw [QuotientGroup.ker_mk']
    exact hcentral
  obtain ⟨component, hcomponent, ⟨quotientEquiv⟩⟩ :=
    central_extension_minimal_normal_simple_factor_has_component_lift
      (QuotientGroup.mk' (pCore prime centralizingGroup)) (QuotientGroup.mk'_surjective _)
      hkernel minimalGroup hminimal.prop.1 simpleFactor hfactorNormal hfactorSimple hfactorNonab
  have hquotientCard := Nat.card_congr quotientEquiv.toEquiv
  have hquotientDivides : prime ∣ Nat.card (component ⧸ Subgroup.center component) := by
    rwa [hquotientCard]
  have hquotientOrder : Nat.card (component ⧸ Subgroup.center component) ∈ knownSimpleOrders := by
    rwa [hquotientCard]
  have hcomponentDivides := hquotientDivides.trans
    (CFSG.card_dvd_of_surjective (QuotientGroup.mk' (Subgroup.center component))
      (QuotientGroup.mk'_surjective _))
  exact ⟨component, hcomponent, hcomponentDivides, hquotientDivides, hquotientOrder⟩

theorem kProper_non_prime_constrained_has_core_centralizer_component
    {G : Type*} [Group G] [Finite G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤)
    (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := overgroup) prime) :
    let centralizingGroup := Subgroup.centralizer
      (pCore prime (overgroup ⧸ primeComplementCore prime) :
        Set (overgroup ⧸ primeComplementCore prime))
    ∃ component : Subgroup centralizingGroup, IsComponentOf component ⊤ ∧
      prime ∣ Nat.card component ∧
      prime ∣ Nat.card (component ⧸ Subgroup.center component) ∧
      Nat.card (component ⧸ Subgroup.center component) ∈ knownSimpleOrders :=
  catalog_non_prime_constrained_has_core_centralizer_component
    (kProper_proper_subgroup_hasCatalogSimpleSections hK overgroup hproper)
    prime hprime hconstraint

theorem quasisimple_subgroup_not_le_pCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (quasisimpleGroup : Subgroup G) (hquasisimple : IsQuasisimple quasisimpleGroup) :
    ¬ quasisimpleGroup ≤ pCore prime G := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsPerfect quasisimpleGroup := Group.isPerfect_def.mpr hquasisimple.1
  let : IsSimpleGroup (quasisimpleGroup ⧸ Subgroup.center quasisimpleGroup) := hquasisimple.2
  let : Nontrivial quasisimpleGroup :=
    (QuotientGroup.mk'_surjective (Subgroup.center quasisimpleGroup)).nontrivial
  intro hbound
  exact Group.IsPerfect.not_isNilpotent quasisimpleGroup
    ((pCore_isPGroup prime).to_le hbound).isNilpotent

theorem kProper_non_prime_constrained_has_reduced_catalog_component
    {G : Type*} [Group G] [Finite G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤)
    (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := overgroup) prime) :
    ∃ component : Subgroup (overgroup ⧸ primeComplementCore prime),
      IsComponentOf component ⊤ ∧
      component ≤ Subgroup.centralizer
        (pCore prime (overgroup ⧸ primeComplementCore prime) : Set _) ∧
      ¬ component ≤ pCore prime (overgroup ⧸ primeComplementCore prime) ∧
      prime ∣ Nat.card component ∧
      prime ∣ Nat.card (component ⧸ Subgroup.center component) ∧
      Nat.card (component ⧸ Subgroup.center component) ∈ knownSimpleOrders ∧
      pRank prime component ≤ pRank prime overgroup := by
  let centralizingGroup := Subgroup.centralizer
    (pCore prime (overgroup ⧸ primeComplementCore prime) :
      Set (overgroup ⧸ primeComplementCore prime))
  obtain ⟨internalComponent, hinternalComponent, hinternalDivides,
    hinternalQuotientDivides, hinternalOrder⟩ :=
    kProper_non_prime_constrained_has_core_centralizer_component hK overgroup hproper
      prime hprime hconstraint
  have hcentralizerNormal : centralizingGroup.Normal :=
    centralizer_normal_of_normal _ (pCore_normal prime)
  let component := Subgroup.map centralizingGroup.subtype internalComponent
  have hcomponent := component_internal_normal_overgroup_maps_to_component
    centralizingGroup hcentralizerNormal internalComponent hinternalComponent
  let componentEquiv := internalComponent.equivMapOfInjective centralizingGroup.subtype
    centralizingGroup.subtype_injective
  have hcard := Nat.card_congr componentEquiv.toEquiv
  have hquotientCard := Nat.card_congr (centerQuotientEquiv componentEquiv).toEquiv
  refine ⟨component, hcomponent, Subgroup.map_subtype_le _,
    quasisimple_subgroup_not_le_pCore prime hprime component hcomponent.2.2, ?_, ?_, ?_,
    reduced_local_subgroup_pRank_le prime hprime overgroup component⟩
  · rwa [← hcard]
  · rwa [← hquotientCard]
  · rwa [← hquotientCard]

theorem kProper_rank_two_non_prime_constrained_has_reduced_catalog_component
    {G : Type*} [Group G] [Finite G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤)
    (prime : ℕ) (hprime : prime.Prime) (hrank : pRank prime overgroup = 2)
    (hconstraint : ¬ HasPrimeConstraint (G := overgroup) prime) :
    ∃ component : Subgroup (overgroup ⧸ primeComplementCore prime),
      IsComponentOf component ⊤ ∧
      component ≤ Subgroup.centralizer
        (pCore prime (overgroup ⧸ primeComplementCore prime) : Set _) ∧
      ¬ component ≤ pCore prime (overgroup ⧸ primeComplementCore prime) ∧
      prime ∣ Nat.card component ∧
      prime ∣ Nat.card (component ⧸ Subgroup.center component) ∧
      Nat.card (component ⧸ Subgroup.center component) ∈ knownSimpleOrders ∧
      pRank prime component ≤ 2 := by
  simpa only [hrank] using kProper_non_prime_constrained_has_reduced_catalog_component
    hK overgroup hproper prime hprime hconstraint

theorem kProper_rank_two_nontransitive_pair_has_reduced_catalog_component
    {G : Type*} [Group G] [Finite G] (hK : IsKProperByOrder G)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (overgroup elementaryGroup first second : Subgroup G) (hproper : overgroup ≠ ⊤)
    (hrank : pRank prime overgroup = 2)
    (hcontained : elementaryGroup ≤ overgroup) (helementary : IsElemAbelian prime elementaryGroup)
    (hcard : Nat.card elementaryGroup = prime ^ 2)
    (hfirst : rankTwoMaximalInvariantTwoSubgroup elementaryGroup first)
    (hsecond : rankTwoMaximalInvariantTwoSubgroup elementaryGroup second)
    (hfirstLe : first ≤ overgroup) (hsecondLe : second ≤ overgroup)
    (hnontransitive : ¬ ∃ conjugator : G,
      conjugator ∈ Subgroup.centralizer (elementaryGroup : Set G) ∧
        first.map (MulAut.conj conjugator).toMonoidHom = second) :
    ∃ component : Subgroup (overgroup ⧸ primeComplementCore prime),
      IsComponentOf component ⊤ ∧
      component ≤ Subgroup.centralizer
        (pCore prime (overgroup ⧸ primeComplementCore prime) : Set _) ∧
      ¬ component ≤ pCore prime (overgroup ⧸ primeComplementCore prime) ∧
      prime ∣ Nat.card component ∧
      prime ∣ Nat.card (component ⧸ Subgroup.center component) ∧
      Nat.card (component ⧸ Subgroup.center component) ∈ knownSimpleOrders ∧
      pRank prime component ≤ 2 := by
  have hfullRank : Nat.card elementaryGroup = prime ^ pRank prime overgroup := by
    rwa [hrank]
  have hobstruction := elementary_full_rank_nontransitive_pair_obstruction prime hprime hodd
    overgroup elementaryGroup first second hcontained helementary hfullRank
    hfirst hsecond hfirstLe hsecondLe hnontransitive
  exact kProper_rank_two_non_prime_constrained_has_reduced_catalog_component hK overgroup hproper
    prime hprime hrank hobstruction.1

end CFSG.RankThreeCoreUniqueness.Helpers
