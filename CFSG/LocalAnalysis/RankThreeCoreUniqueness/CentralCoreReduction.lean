module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ReducedCentralizerObstruction

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem pCore_quotient_eq_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) :
    letI := pCore_normal prime (G := G)
    pCore prime (G ⧸ pCore prime G) = ⊥ := by
  let : (pCore prime G).Normal := pCore_normal prime
  let homomorphism := QuotientGroup.mk' (pCore prime G)
  let quotientCore := pCore prime (G ⧸ pCore prime G)
  have hkernel : IsPGroup prime homomorphism.ker := by
    dsimp only [homomorphism]
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup prime
  have hpreimageGroup : IsPGroup prime (Subgroup.comap homomorphism quotientCore) :=
    (pCore_isPGroup prime).comap_of_ker_isPGroup homomorphism hkernel
  have hpreimageNormal : (Subgroup.comap homomorphism quotientCore).Normal :=
    (pCore_normal prime).comap homomorphism
  have hbound := normal_pGroup_le_pCore prime _ hpreimageNormal hpreimageGroup
  apply le_bot_iff.mp
  intro element helement
  obtain ⟨representative, hrepresentative⟩ := QuotientGroup.mk'_surjective (pCore prime G) element
  have hpreimage : representative ∈ Subgroup.comap homomorphism quotientCore := by
    change homomorphism representative ∈ quotientCore
    rwa [hrepresentative]
  apply Subgroup.mem_bot.mpr
  rw [← hrepresentative]
  exact (QuotientGroup.eq_one_iff representative).mpr (hbound hpreimage)

theorem coprime_subgroup_of_pGroup_eq_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hgroup : IsPGroup prime G) (subgroup : Subgroup G)
    (hcoprime : prime.Coprime (Nat.card subgroup)) : subgroup = ⊥ := by
  let : Fact prime.Prime := ⟨hprime⟩
  rcases (hgroup.to_subgroup subgroup).card_eq_or_dvd with hcard | hdivides
  · exact Subgroup.card_eq_one.mp hcard
  · exact False.elim (hprime.coprime_iff_not_dvd.mp hcoprime hdivides)

theorem complement_normal_of_central_kernel
    {G : Type*} [Group G] (normalGroup complement : Subgroup G)
    (hcentral : normalGroup ≤ Subgroup.center G)
    (hcomplement : complement.IsComplement' normalGroup) : complement.Normal := by
  have hnormalizer : (⊤ : Subgroup G) ≤ Subgroup.normalizer (complement : Set G) := by
    rw [← hcomplement.sup_eq_top]
    apply sup_le Subgroup.le_normalizer
    exact hcentral.trans (Subgroup.center_le_normalizer _)
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnormalizer)

theorem central_pGroup_complement_eq_primeComplementCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (normalGroup complement : Subgroup G) (hnormal : normalGroup.Normal)
    (hcentral : normalGroup ≤ Subgroup.center G) (hgroup : IsPGroup prime normalGroup)
    (hcoprime : prime.Coprime (Nat.card complement))
    (hcomplement : complement.IsComplement' normalGroup) :
    primeComplementCore (G := G) prime = complement := by
  let : normalGroup.Normal := hnormal
  let : complement.Normal := complement_normal_of_central_kernel normalGroup complement
    hcentral hcomplement
  have hquotient : IsPGroup prime (G ⧸ complement) :=
    hgroup.of_equiv hcomplement.symm.QuotientMulEquiv.symm
  have himageCoprime : prime.Coprime
      (Nat.card (Subgroup.map (QuotientGroup.mk' complement) (primeComplementCore prime))) :=
    (primeComplementCore_coprime prime).of_dvd_right
      ((primeComplementCore prime).card_map_dvd (QuotientGroup.mk' complement))
  have himageBot := coprime_subgroup_of_pGroup_eq_bot prime hprime hquotient _ himageCoprime
  have hbound := (Subgroup.map_eq_bot_iff (primeComplementCore prime)).mp himageBot
  rw [QuotientGroup.ker_mk'] at hbound
  exact le_antisymm hbound
    (normal_coprime_le_primeComplementCore prime complement inferInstance hcoprime)

theorem central_pCore_quotient_primeComplementCore_eq_bot
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hcentral : pCore prime G ≤ Subgroup.center G)
    (hcore : primeComplementCore (G := G) prime = ⊥) :
    letI := pCore_normal prime (G := G)
    primeComplementCore (G := G ⧸ pCore prime G) prime = ⊥ := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  let : (pCore prime G).Normal := pCore_normal prime
  let homomorphism := QuotientGroup.mk' (pCore prime G)
  let quotientCore := primeComplementCore (G := G ⧸ pCore prime G) prime
  let preimageGroup := Subgroup.comap homomorphism quotientCore
  let : preimageGroup.Normal := (primeComplementCore_normal prime).comap homomorphism
  let restrictedMap : preimageGroup →* quotientCore :=
    (homomorphism.domRestrict preimageGroup).codRestrict quotientCore
      (fun element => element.property)
  have hrestrictedSurjective : Function.Surjective restrictedMap := by
    intro element
    obtain ⟨preimage, hpreimage⟩ := QuotientGroup.mk'_surjective (pCore prime G) element.val
    have hmem : preimage ∈ preimageGroup := by
      change homomorphism preimage ∈ quotientCore
      rw [hpreimage]
      exact element.property
    exact ⟨⟨preimage, hmem⟩, Subtype.ext hpreimage⟩
  have hkernel : restrictedMap.ker = (pCore prime G).subgroupOf preimageGroup := by
    ext element
    change restrictedMap element = 1 ↔ element.val ∈ pCore prime G
    rw [← QuotientGroup.eq_one_iff element.val]
    constructor
    · intro hequal
      exact congrArg Subtype.val hequal
    · intro hequal
      exact Subtype.ext hequal
  have hkernelPGroup : IsPGroup prime restrictedMap.ker := by
    rw [hkernel]
    exact (pCore_isPGroup prime).comap_subtype
  have hkernelCentral : restrictedMap.ker ≤ Subgroup.center preimageGroup := by
    intro element helement
    rw [hkernel] at helement
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral helement) other.val
  let quotientEquiv := QuotientGroup.quotientKerEquivOfSurjective restrictedMap hrestrictedSurjective
  have hindex : restrictedMap.ker.index = Nat.card quotientCore := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr quotientEquiv.toEquiv
  have hcoprime : (Nat.card restrictedMap.ker).Coprime restrictedMap.ker.index := by
    obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp hkernelPGroup
    rw [hcard, hindex]
    exact (primeComplementCore_coprime prime).pow_left exponent
  obtain ⟨complement, hcomplement⟩ := Subgroup.exists_left_complement'_of_coprime hcoprime
  have hcomplementCoprime : prime.Coprime (Nat.card complement) := by
    rw [← hcomplement.index_eq_card, hindex]
    exact primeComplementCore_coprime prime
  have hequal := central_pGroup_complement_eq_primeComplementCore prime hprime
    restrictedMap.ker complement inferInstance hkernelCentral hkernelPGroup
    hcomplementCoprime hcomplement
  let : complement.Characteristic := by
    rw [← hequal]
    exact primeComplementCore_characteristic prime
  have hmappedNormal : (Subgroup.map preimageGroup.subtype complement).Normal := by infer_instance
  have hmappedBot : Subgroup.map preimageGroup.subtype complement = ⊥ := by
    apply le_bot_iff.mp
    rw [← hcore]
    exact normal_coprime_le_primeComplementCore prime _ hmappedNormal
      (hcomplementCoprime.of_dvd_right (complement.card_map_dvd preimageGroup.subtype))
  have hcomplementBot := (Subgroup.map_eq_bot_iff_of_injective complement
    preimageGroup.subtype_injective).mp hmappedBot
  have hcard : Nat.card quotientCore = 1 := by
    rw [← hindex, hcomplement.index_eq_card, hcomplementBot, Subgroup.card_bot]
  exact Subgroup.card_eq_one.mp hcard

theorem trivial_cores_nontrivial_group_has_minimal_normal_perfect_subgroup
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (prime : ℕ) (hprime : prime.Prime)
    (hcoprimeCore : primeComplementCore (G := G) prime = ⊥)
    (hpCore : pCore prime G = ⊥) :
    ∃ minimalGroup : Subgroup G, Minimal (fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥)
        minimalGroup ∧ Group.IsPerfect minimalGroup ∧ prime ∣ Nat.card minimalGroup := by
  classical
  obtain ⟨minimalGroup, _, hminimal⟩ := Finite.exists_le_minimal
    (p := fun subgroup : Subgroup G => subgroup.Normal ∧ subgroup ≠ ⊥)
    (a := ⊤) ⟨by infer_instance, top_ne_bot⟩
  let : minimalGroup.Normal := hminimal.prop.1
  have hnonabelian : ¬ IsMulCommutative minimalGroup := by
    intro hcommutative
    have hnilpotent : Group.IsNilpotent minimalGroup := by
      apply Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot (n := 1)
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
      exact Subgroup.commutator_self_eq_bot_iff.mpr hcommutative
    have hgroup := normal_nilpotent_isPGroup_of_primeComplementCore_eq_bot
      prime hprime hcoprimeCore minimalGroup hminimal.prop.1 hnilpotent
    have hbound := normal_pGroup_le_pCore prime minimalGroup hminimal.prop.1 hgroup
    rw [hpCore] at hbound
    exact hminimal.prop.2 (le_bot_iff.mp hbound)
  have hcommutatorNontrivial : ⁅minimalGroup, minimalGroup⁆ ≠ ⊥ := by
    intro hzero
    exact hnonabelian (Subgroup.commutator_self_eq_bot_iff.mp hzero)
  have hperfect : Group.IsPerfect minimalGroup := Subgroup.isPerfect_iff.mpr
    (hminimal.eq_of_le ⟨by infer_instance, hcommutatorNontrivial⟩
      (Subgroup.commutator_le_self minimalGroup))
  have hdivides : prime ∣ Nat.card minimalGroup := by
    by_contra hnotDivides
    have hbound := normal_coprime_le_primeComplementCore prime minimalGroup hminimal.prop.1
      (hprime.coprime_iff_not_dvd.mpr hnotDivides)
    rw [hcoprimeCore] at hbound
    exact hminimal.prop.2 (le_bot_iff.mp hbound)
  exact ⟨minimalGroup, hminimal, hperfect, hdivides⟩

theorem non_prime_constrained_centralizer_quotient_has_minimal_normal_perfect_subgroup
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hconstraint : ¬ HasPrimeConstraint (G := G) prime) :
    let centralizingGroup := Subgroup.centralizer
      (pCore prime (G ⧸ primeComplementCore prime) : Set (G ⧸ primeComplementCore prime))
    letI := pCore_normal prime (G := centralizingGroup)
    ∃ minimalGroup : Subgroup (centralizingGroup ⧸ pCore prime centralizingGroup),
      Minimal (fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥) minimalGroup ∧
        Group.IsPerfect minimalGroup ∧ prime ∣ Nat.card minimalGroup := by
  let centralizingGroup := Subgroup.centralizer
    (pCore prime (G ⧸ primeComplementCore prime) : Set (G ⧸ primeComplementCore prime))
  let : (pCore prime centralizingGroup).Normal := pCore_normal prime
  have hnonsolvable : ¬ Group.IsSolvable centralizingGroup :=
    not_prime_constrained_has_nonsolvable_core_centralizer prime hprime hconstraint
  have hcentral : pCore prime centralizingGroup ≤ Subgroup.center centralizingGroup :=
    pCore_centralizer_internal_pCore_le_center prime
  have hpCoreProper : pCore prime centralizingGroup ≠ ⊤ := by
    intro htop
    apply hnonsolvable
    apply Group.isSolvable_of_comm
    intro first second
    exact Subgroup.mem_center_iff.mp
      (hcentral (htop ▸ Subgroup.mem_top second)) first
  let : Nontrivial (centralizingGroup ⧸ pCore prime centralizingGroup) :=
    QuotientGroup.nontrivial_iff.mpr hpCoreProper
  exact trivial_cores_nontrivial_group_has_minimal_normal_perfect_subgroup prime hprime
    (central_pCore_quotient_primeComplementCore_eq_bot prime hprime hcentral
      (reduced_pCore_centralizer_primeComplementCore_eq_bot prime))
    (pCore_quotient_eq_bot prime)

end CFSG.RankThreeCoreUniqueness.Helpers
