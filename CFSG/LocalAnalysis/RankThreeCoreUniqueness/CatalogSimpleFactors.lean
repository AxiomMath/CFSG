module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralCoreReduction
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MinimalNormalFactors
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CatalogSections

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem characteristically_simple_primeComplementCore_eq_bot
    {G : Type*} [Group G] [Finite G]
    (hcharacteristic : ∀ subgroup : Subgroup G, subgroup.Characteristic →
      subgroup = ⊥ ∨ subgroup = ⊤)
    (prime : ℕ) (hprime : prime.Prime) (hdivides : prime ∣ Nat.card G) :
    primeComplementCore (G := G) prime = ⊥ := by
  rcases hcharacteristic (primeComplementCore prime)
      (primeComplementCore_characteristic prime) with hbottom | htop
  · exact hbottom
  · have hcoprime := primeComplementCore_coprime (G := G) prime
    rw [htop, Subgroup.card_top] at hcoprime
    exact False.elim ((hprime.coprime_iff_not_dvd.mp hcoprime) hdivides)

theorem characteristically_simple_normal_factor_prime_dvd
    {G : Type*} [Group G] [Finite G]
    (hcharacteristic : ∀ subgroup : Subgroup G, subgroup.Characteristic →
      subgroup = ⊥ ∨ subgroup = ⊤)
    (prime : ℕ) (hprime : prime.Prime) (hdivides : prime ∣ Nat.card G)
    (normalFactor : Subgroup G) (hnormal : normalFactor.Normal)
    (hnontrivial : normalFactor ≠ ⊥) : prime ∣ Nat.card normalFactor := by
  by_contra hnotDivides
  have hbound := normal_coprime_le_primeComplementCore prime normalFactor hnormal
    (hprime.coprime_iff_not_dvd.mpr hnotDivides)
  rw [characteristically_simple_primeComplementCore_eq_bot
    hcharacteristic prime hprime hdivides] at hbound
  exact hnontrivial (le_bot_iff.mp hbound)

theorem minimal_normal_perfect_has_prime_divisible_catalog_simple_factor
    {G : Type*} [Group G] [Finite G] (hcatalog : HasCatalogSimpleSections G)
    (prime : ℕ) (hprime : prime.Prime) (minimalGroup : Subgroup G)
    (hminimal : Minimal (fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥) minimalGroup)
    (hperfect : Group.IsPerfect minimalGroup) (hdivides : prime ∣ Nat.card minimalGroup) :
    ∃ simpleFactor : Subgroup minimalGroup, simpleFactor.Normal ∧
      IsSimpleGroup simpleFactor ∧
      (∃ first second : simpleFactor, first * second ≠ second * first) ∧
      prime ∣ Nat.card simpleFactor ∧ Nat.card simpleFactor ∈ knownSimpleOrders := by
  obtain ⟨simpleFactor, hnormal, hsimple, hnonab⟩ :=
    finite_minimal_normal_perfect_has_simple_normal_factor minimalGroup hminimal hperfect
  let : IsSimpleGroup simpleFactor := hsimple
  have hnontrivial : simpleFactor ≠ ⊥ := simpleFactor.nontrivial_iff_ne_bot.mp inferInstance
  have hfactorDivides := characteristically_simple_normal_factor_prime_dvd
    (minimal_normal_subgroup_characteristically_simple minimalGroup hminimal)
    prime hprime hdivides simpleFactor hnormal hnontrivial
  have horder := catalog_simple_subgroup_order
    (catalogSections_subgroup hcatalog minimalGroup) simpleFactor hsimple hnonab
  exact ⟨simpleFactor, hnormal, hsimple, hnonab, hfactorDivides, horder⟩

theorem catalog_non_prime_constrained_has_prime_divisible_simple_factor
    {G : Type*} [Group G] [Finite G] (hcatalog : HasCatalogSimpleSections G)
    (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := G) prime) :
    let centralizingGroup := Subgroup.centralizer
      (pCore prime (G ⧸ primeComplementCore prime) : Set (G ⧸ primeComplementCore prime))
    letI := pCore_normal prime (G := centralizingGroup)
    ∃ minimalGroup : Subgroup (centralizingGroup ⧸ pCore prime centralizingGroup),
      Minimal (fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥) minimalGroup ∧
        Group.IsPerfect minimalGroup ∧ prime ∣ Nat.card minimalGroup ∧
        ∃ simpleFactor : Subgroup minimalGroup, simpleFactor.Normal ∧
          IsSimpleGroup simpleFactor ∧
          (∃ first second : simpleFactor, first * second ≠ second * first) ∧
          prime ∣ Nat.card simpleFactor ∧ Nat.card simpleFactor ∈ knownSimpleOrders := by
  let centralizingGroup := Subgroup.centralizer
    (pCore prime (G ⧸ primeComplementCore prime) : Set (G ⧸ primeComplementCore prime))
  let : (pCore prime centralizingGroup).Normal := pCore_normal prime
  obtain ⟨minimalGroup, hminimal, hperfect, hdivides⟩ :=
    non_prime_constrained_centralizer_quotient_has_minimal_normal_perfect_subgroup
      prime hprime hconstraint
  have hquotientCatalog := catalogSections_quotient
    (catalogSections_subgroup (catalogSections_quotient hcatalog (primeComplementCore prime))
      centralizingGroup) (pCore prime centralizingGroup)
  exact ⟨minimalGroup, hminimal, hperfect, hdivides,
    minimal_normal_perfect_has_prime_divisible_catalog_simple_factor hquotientCatalog
      prime hprime minimalGroup hminimal hperfect hdivides⟩

theorem kProper_non_prime_constrained_has_prime_divisible_simple_factor
    {G : Type*} [Group G] [Finite G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤)
    (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := overgroup) prime) :
    let centralizingGroup := Subgroup.centralizer
      (pCore prime (overgroup ⧸ primeComplementCore prime) :
        Set (overgroup ⧸ primeComplementCore prime))
    letI := pCore_normal prime (G := centralizingGroup)
    ∃ minimalGroup : Subgroup (centralizingGroup ⧸ pCore prime centralizingGroup),
      Minimal (fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥) minimalGroup ∧
        Group.IsPerfect minimalGroup ∧ prime ∣ Nat.card minimalGroup ∧
        ∃ simpleFactor : Subgroup minimalGroup, simpleFactor.Normal ∧
          IsSimpleGroup simpleFactor ∧
          (∃ first second : simpleFactor, first * second ≠ second * first) ∧
          prime ∣ Nat.card simpleFactor ∧ Nat.card simpleFactor ∈ knownSimpleOrders :=
  catalog_non_prime_constrained_has_prime_divisible_simple_factor
    (kProper_proper_subgroup_hasCatalogSimpleSections hK overgroup hproper)
    prime hprime hconstraint

end CFSG.RankThreeCoreUniqueness.Helpers
