module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SolvableConstraint
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.NonsolvableSections
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SectionTransport
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem normal_subgroup_primeComplementCore_le
    {G : Type*} [Group G] [Finite G] (prime : ℕ)
    (normalGroup : Subgroup G) (hnormal : normalGroup.Normal) :
    Subgroup.map normalGroup.subtype (primeComplementCore prime) ≤ primeComplementCore prime := by
  let : normalGroup.Normal := hnormal
  let : (primeComplementCore (G := normalGroup) prime).Characteristic :=
    primeComplementCore_characteristic prime
  have hmappedNormal : (Subgroup.map normalGroup.subtype (primeComplementCore prime)).Normal := by
    infer_instance
  exact normal_coprime_le_primeComplementCore prime _ hmappedNormal
    ((primeComplementCore_coprime prime).of_dvd_right
      ((primeComplementCore (G := normalGroup) prime).card_map_dvd normalGroup.subtype))

theorem normal_subgroup_pCore_le
    {G : Type*} [Group G] (prime : ℕ) (normalGroup : Subgroup G)
    (hnormal : normalGroup.Normal) :
    Subgroup.map normalGroup.subtype (pCore prime normalGroup) ≤ pCore prime G := by
  let : normalGroup.Normal := hnormal
  let : (pCore prime normalGroup).Characteristic := pCore_characteristic prime
  have hmappedNormal : (Subgroup.map normalGroup.subtype (pCore prime normalGroup)).Normal := by
    infer_instance
  exact normal_pGroup_le_pCore prime _ hmappedNormal ((pCore_isPGroup prime).map normalGroup.subtype)

theorem pCore_centralizer_internal_pCore_le_center
    {G : Type*} [Group G] (prime : ℕ) :
    pCore prime (Subgroup.centralizer (pCore prime G : Set G)) ≤
      Subgroup.center (Subgroup.centralizer (pCore prime G : Set G)) := by
  let centralizingGroup := Subgroup.centralizer (pCore prime G : Set G)
  have hnormal := centralizer_normal_of_normal _ (pCore_normal prime (G := G))
  have hcoreLe := normal_subgroup_pCore_le prime centralizingGroup hnormal
  intro coreElement hcoreElement
  apply Subgroup.mem_center_iff.mpr
  intro centralizingElement
  apply Subtype.ext
  have hambientCore : (coreElement : G) ∈ pCore prime G :=
    hcoreLe (Subgroup.mem_map_of_mem centralizingGroup.subtype hcoreElement)
  exact (Subgroup.mem_centralizer_iff.mp centralizingElement.property coreElement.val hambientCore).symm

theorem reduced_pCore_centralizer_primeComplementCore_eq_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    primeComplementCore (G := Subgroup.centralizer
      (pCore prime (G ⧸ primeComplementCore prime) : Set (G ⧸ primeComplementCore prime))) prime = ⊥ := by
  let centralizingGroup := Subgroup.centralizer
    (pCore prime (G ⧸ primeComplementCore prime) : Set (G ⧸ primeComplementCore prime))
  have hnormal := centralizer_normal_of_normal _ (pCore_normal prime (G := G ⧸ primeComplementCore prime))
  have hbound := normal_subgroup_primeComplementCore_le prime centralizingGroup hnormal
  rw [primeComplementCore_quotient_eq_bot] at hbound
  exact (Subgroup.map_eq_bot_iff_of_injective _ centralizingGroup.subtype_injective).mp
    (le_bot_iff.mp hbound)

theorem non_prime_constrained_has_normal_perfect_centralizing_subgroup
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := G) prime) :
    ∃ perfectGroup : Subgroup (G ⧸ primeComplementCore prime), perfectGroup.Normal ∧
      perfectGroup ≠ ⊥ ∧ Group.IsPerfect perfectGroup ∧
      perfectGroup ≤ Subgroup.centralizer
        (pCore prime (G ⧸ primeComplementCore prime) : Set _) ∧
      ¬ perfectGroup ≤ pCore prime (G ⧸ primeComplementCore prime) ∧
      prime ∣ Nat.card perfectGroup := by
  let reducedCore := pCore prime (G ⧸ primeComplementCore prime)
  let centralizingGroup := Subgroup.centralizer
    (reducedCore : Set (G ⧸ primeComplementCore prime))
  let : centralizingGroup.Normal := centralizer_normal_of_normal _ (pCore_normal prime)
  have hnonsolvable : ¬ Group.IsSolvable centralizingGroup :=
    not_prime_constrained_has_nonsolvable_core_centralizer prime hprime hconstraint
  obtain ⟨perfectInternal, hcharacteristic, hnontrivial, hperfect⟩ :=
    finite_nonsolvable_has_characteristic_perfect_subgroup hnonsolvable
  let : perfectInternal.Characteristic := hcharacteristic
  let : Group.IsPerfect perfectInternal := hperfect
  let perfectGroup := Subgroup.map centralizingGroup.subtype perfectInternal
  have hnormal : perfectGroup.Normal := by infer_instance
  have hperfectGroup : Group.IsPerfect perfectGroup := by
    apply Subgroup.isPerfect_iff.mpr
    dsimp only [perfectGroup]
    rw [← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  let : Group.IsPerfect perfectGroup := hperfectGroup
  have hnontrivialGroup : perfectGroup ≠ ⊥ := by
    exact ((Subgroup.map_eq_bot_iff_of_injective perfectInternal
      centralizingGroup.subtype_injective).not).mpr hnontrivial
  let : Nontrivial perfectGroup := perfectGroup.nontrivial_iff_ne_bot.mpr hnontrivialGroup
  have hnotCore : ¬ perfectGroup ≤ reducedCore := by
    intro hbound
    let : Fact prime.Prime := ⟨hprime⟩
    have hpGroup := (pCore_isPGroup prime (G := G ⧸ primeComplementCore prime)).to_le hbound
    exact Group.IsPerfect.not_isNilpotent perfectGroup hpGroup.isNilpotent
  have hdivides : prime ∣ Nat.card perfectGroup := by
    by_contra hnotDivides
    have hbound := normal_coprime_le_primeComplementCore prime perfectGroup hnormal
      (hprime.coprime_iff_not_dvd.mpr hnotDivides)
    rw [primeComplementCore_quotient_eq_bot] at hbound
    exact hnontrivialGroup (le_bot_iff.mp hbound)
  exact ⟨perfectGroup, hnormal, hnontrivialGroup, hperfectGroup,
    Subgroup.map_subtype_le _, hnotCore, hdivides⟩

theorem kProper_non_prime_constrained_local_has_catalog_simple_section
    {G : Type*} [Group G] [Finite G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤)
    (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := overgroup) prime) :
    ∃ perfectGroup : Subgroup (overgroup ⧸ primeComplementCore prime), perfectGroup.Normal ∧
      perfectGroup ≠ ⊥ ∧ Group.IsPerfect perfectGroup ∧
      perfectGroup ≤ Subgroup.centralizer
        (pCore prime (overgroup ⧸ primeComplementCore prime) : Set _) ∧
      ¬ perfectGroup ≤ pCore prime (overgroup ⧸ primeComplementCore prime) ∧
      prime ∣ Nat.card perfectGroup ∧
      ∃ kernelGroup : Subgroup perfectGroup, ∃ hnormal : kernelGroup.Normal, letI := hnormal;
        IsSimpleGroup (perfectGroup ⧸ kernelGroup) ∧
        (∃ first second : perfectGroup ⧸ kernelGroup, first * second ≠ second * first) ∧
        Nat.card (perfectGroup ⧸ kernelGroup) ∈ knownSimpleOrders := by
  obtain ⟨perfectGroup, hnormalGroup, hnontrivial, hperfect, hcentralizes, hnotCore, hdivides⟩ :=
    non_prime_constrained_has_normal_perfect_centralizing_subgroup prime hprime hconstraint
  let : Nontrivial perfectGroup := perfectGroup.nontrivial_iff_ne_bot.mpr hnontrivial
  let : Group.IsPerfect perfectGroup := hperfect
  obtain ⟨kernelGroup, hnormal, hsimple, hnonab⟩ :=
    perfect_group_has_nonabelian_simple_quotient (G := perfectGroup)
  let : kernelGroup.Normal := hnormal
  let : IsSimpleGroup (perfectGroup ⧸ kernelGroup) := hsimple
  have horder := kProper_proper_subgroup_image_simple_subgroup_image_order hK overgroup hproper
    (QuotientGroup.mk' (primeComplementCore (G := overgroup) prime))
    (QuotientGroup.mk'_surjective _) perfectGroup (QuotientGroup.mk' kernelGroup)
    (QuotientGroup.mk'_surjective _) hnonab
  exact ⟨perfectGroup, hnormalGroup, hnontrivial, hperfect, hcentralizes, hnotCore, hdivides,
    kernelGroup, hnormal, hsimple, hnonab, horder⟩

theorem reduced_local_subgroup_pRank_le
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (overgroup : Subgroup G)
    (subgroup : Subgroup (overgroup ⧸ primeComplementCore prime)) :
    pRank prime subgroup ≤ pRank prime overgroup := by
  calc
    pRank prime subgroup ≤ pRank prime
        (⊤ : Subgroup (overgroup ⧸ primeComplementCore prime)) :=
      pRank_mono prime hprime.one_lt le_top
    _ = pRank prime (⊤ : Subgroup overgroup) := primeComplementCore_quotient_pRank_eq prime hprime
    _ = pRank prime overgroup := (pRank_subgroup_eq_internal_top prime hprime.one_lt overgroup).symm

theorem rank_two_local_reduced_subgroup_pRank_le_two
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (overgroup : Subgroup G) (hrank : pRank prime overgroup = 2)
    (subgroup : Subgroup (overgroup ⧸ primeComplementCore prime)) :
    pRank prime subgroup ≤ 2 := by
  simpa only [hrank] using reduced_local_subgroup_pRank_le prime hprime overgroup subgroup

end CFSG.RankThreeCoreUniqueness.Helpers
