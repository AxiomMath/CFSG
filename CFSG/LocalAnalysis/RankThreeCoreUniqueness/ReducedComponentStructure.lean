module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalComponentObstruction
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem trivial_primeComplementCore_center_le_pCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hcore : primeComplementCore (G := G) prime = ⊥) :
    Subgroup.center G ≤ pCore prime G := by
  have hnilpotent : Group.IsNilpotent (Subgroup.center G) := by
    apply Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot (n := 1)
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
    exact Subgroup.commutator_self_eq_bot_iff.mpr inferInstance
  have hpGroup := normal_nilpotent_isPGroup_of_primeComplementCore_eq_bot prime hprime hcore
    (Subgroup.center G) inferInstance hnilpotent
  exact normal_pGroup_le_pCore prime (Subgroup.center G) inferInstance hpGroup

theorem reduced_core_centralizing_component_pCore_eq_center
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hcore : primeComplementCore (G := G) prime = ⊥)
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤)
    (hcentralizes : component ≤ Subgroup.centralizer (pCore prime G : Set G)) :
    pCore prime component = Subgroup.center component ∧
      primeComplementCore (G := component) prime = ⊥ ∧
      IsPGroup prime (Subgroup.center component) := by
  have hinternalCore := cfsg_subnormal_primeComplementCore_eq_bot prime component
    hcomponent.2.1 hcore
  have hcenterLe := trivial_primeComplementCore_center_le_pCore prime hprime hinternalCore
  have hpCoreEq := le_antisymm
    (cfsg_subnormal_internal_pCore_le_center_of_core_centralizing prime component
      hcomponent.2.1 hcentralizes) hcenterLe
  exact ⟨hpCoreEq, hinternalCore, hpCoreEq ▸ pCore_isPGroup prime⟩

theorem kProper_rank_two_nontransitive_pair_has_reduced_pComponent
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
      pRank prime component ≤ 2 ∧
      pCore prime component = Subgroup.center component ∧
      primeComplementCore (G := component) prime = ⊥ ∧
      IsPGroup prime (Subgroup.center component) := by
  obtain ⟨component, hcomponent, hcentralizes, hnotCore, hdivides, hquotientDivides,
    horder, hcomponentRank⟩ := kProper_rank_two_nontransitive_pair_has_reduced_catalog_component
    hK prime hprime hodd overgroup elementaryGroup first second hproper hrank hcontained
    helementary hcard hfirst hsecond hfirstLe hsecondLe hnontransitive
  exact ⟨component, hcomponent, hcentralizes, hnotCore, hdivides, hquotientDivides,
    horder, hcomponentRank, reduced_core_centralizing_component_pCore_eq_center prime hprime
      (primeComplementCore_quotient_eq_bot prime) component hcomponent hcentralizes⟩

end CFSG.RankThreeCoreUniqueness.Helpers
