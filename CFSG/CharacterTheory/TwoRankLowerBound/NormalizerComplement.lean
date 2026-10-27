module

public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicOddComplement
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

theorem cyclic_two_group_automorphisms_isPGroup (G : Type*) [Group G] [Finite G]
    [IsCyclic G] (htwo : IsPGroup 2 G) : IsPGroup 2 (MulAut G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨exponent, hcard⟩ := htwo.exists_card_eq
  apply IsPGroup.iff_card.mpr
  rw [IsCyclic.card_mulAut, hcard]
  cases exponent with
  | zero => exact ⟨0, by simp⟩
  | succ exponent =>
    exact ⟨exponent, by rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp⟩

@[expose] def sylowIntersectionNormal {prime : ℕ} {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime prime)] (sylow : Sylow prime G) (normal : Subgroup G)
    [normal.Normal] : Sylow prime normal where
  toSubgroup := (sylow : Subgroup G).subgroupOf normal
  isPGroup' := sylow.isPGroup'.comap_subtype
  is_maximal' := by
    intro larger hlarger hle
    obtain ⟨other, hother⟩ := (hlarger.map normal.subtype).exists_le_sylow
    obtain ⟨conjugator, hconjugator⟩ := MulAction.exists_smul_eq G other sylow
    have hconjugate : larger.map (MulAut.conjNormal conjugator).toMonoidHom ≤
        (sylow : Subgroup G).subgroupOf normal := by
      rintro element ⟨member, hmember, rfl⟩
      change conjugator * (member : G) * conjugator⁻¹ ∈ (sylow : Subgroup G)
      rw [← hconjugator]
      change conjugator * (member : G) * conjugator⁻¹ ∈
        MulAut.conj conjugator • (other : Subgroup G)
      apply (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr
      exact ⟨member, hother ⟨member, hmember, rfl⟩, rfl⟩
    have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hconjugate)
      (Subgroup.inclusion_injective hconjugate)
    rw [Subgroup.card_map_of_injective
      (f := (MulAut.conjNormal conjugator).toMonoidHom)
      (MulAut.conjNormal conjugator).injective] at hcard
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem sylowIntersectionNormal_coe {prime : ℕ} {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime prime)] (sylow : Sylow prime G) (normal : Subgroup G)
    [normal.Normal] :
    (sylowIntersectionNormal sylow normal : Subgroup normal) =
      (sylow : Subgroup G).subgroupOf normal := rfl

theorem odd_normal_two_quotient_complement_sylow {G : Type*} [Group G] [Finite G]
    (sylow : Sylow 2 G) (kernel : Subgroup G) [kernel.Normal]
    (hodd : Odd (Nat.card kernel)) (hquotient : IsPGroup 2 (G ⧸ kernel)) :
    kernel.IsComplement' (sylow : Subgroup G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨exponent, hcard⟩ := sylow.isPGroup'.exists_card_eq
  have hdisjoint : Disjoint kernel (sylow : Subgroup G) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hcard]
    exact (Nat.coprime_two_right.mpr hodd).pow_right exponent
  let quotientSylow := sylow.mapSurjective (QuotientGroup.mk'_surjective kernel)
  have htop : (quotientSylow : Subgroup (G ⧸ kernel)) = ⊤ :=
    (quotientSylow.is_maximal' (hquotient.to_subgroup ⊤) le_top).symm
  have hmap : (sylow : Subgroup G).map (QuotientGroup.mk' kernel) = ⊤ := by
    simpa only [quotientSylow, Sylow.coe_mapSurjective] using htop
  have hsup : kernel ⊔ (sylow : Subgroup G) = ⊤ := by
    have hcomap := congrArg (Subgroup.comap (QuotientGroup.mk' kernel)) hmap
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomap
    simpa only [sup_comm] using hcomap
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjoint
  rw [← Subgroup.normal_mul, hsup]
  rfl

theorem cyclic_sylow_centralizer_odd_normal_complement {G : Type*}
    [Group G] [Finite G] (sylow : Sylow 2 G) (centralizer : Subgroup G)
    [centralizer.Normal]
    (hcyclic : IsCyclic ((sylow : Subgroup G).subgroupOf centralizer))
    (heven : Even (Nat.card centralizer))
    (hquotient : IsPGroup 2 (G ⧸ centralizer)) :
    ∃ kernel : Subgroup G, kernel.Normal ∧ Odd (Nat.card kernel) ∧
      kernel ≤ centralizer ∧ kernel.IsComplement' (sylow : Subgroup G) ∧
      (kernel.subgroupOf centralizer).Characteristic ∧
      (kernel.subgroupOf centralizer).IsComplement'
        ((sylow : Subgroup G).subgroupOf centralizer) ∧
      ∀ element : centralizer, (element : G) ∈ kernel ↔ Odd (orderOf element) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let localSylow := sylowIntersectionNormal sylow centralizer
  obtain ⟨localKernel, hcharacteristic, hodd, hlocalComplement, hmembership⟩ :=
    exists_characteristic_odd_complement_of_cyclic_sylow_two localSylow hcyclic heven
  let kernel := localKernel.map centralizer.subtype
  let : localKernel.Characteristic := hcharacteristic
  let : kernel.Normal := ConjAct.normal_of_characteristic_of_normal
  have hlocal : kernel.subgroupOf centralizer = localKernel := by
    exact Subgroup.comap_map_eq_self_of_injective centralizer.subtype_injective localKernel
  have hkernelCard : Nat.card kernel = Nat.card localKernel :=
    Subgroup.card_map_of_injective centralizer.subtype_injective
  have hquotientKernel : IsPGroup 2 (G ⧸ kernel) := by
    obtain ⟨localExponent, hlocalCard⟩ := localSylow.isPGroup'.exists_card_eq
    obtain ⟨quotientExponent, hquotientCard⟩ := hquotient.exists_card_eq
    apply IsPGroup.iff_card.mpr
    refine ⟨localExponent + quotientExponent, ?_⟩
    rw [← kernel.index_eq_card,
      ← Subgroup.relIndex_mul_index (Subgroup.map_subtype_le localKernel)]
    change (kernel.subgroupOf centralizer).index * centralizer.index = _
    rw [hlocal, hlocalComplement.symm.index_eq_card, hlocalCard,
      centralizer.index_eq_card, hquotientCard, pow_add]
  refine ⟨kernel, inferInstance, hkernelCard ▸ hodd,
    Subgroup.map_subtype_le localKernel,
    odd_normal_two_quotient_complement_sylow sylow kernel (hkernelCard ▸ hodd)
      hquotientKernel, hlocal ▸ hcharacteristic, hlocal ▸ hlocalComplement, ?_⟩
  intro element
  change element ∈ kernel.subgroupOf centralizer ↔ _
  rw [hlocal, hmembership]

theorem cyclic_two_section_normalizer_quotient_isPGroup {G : Type*}
    [Group G] [Finite G] (sylow : Sylow 2 G) (cyclicSection : Subgroup G)
    (hle : cyclicSection ≤ (sylow : Subgroup G)) (hcyclic : IsCyclic cyclicSection) :
    IsPGroup 2 ((Subgroup.normalizer (cyclicSection : Set G)) ⧸
      (Subgroup.centralizer (cyclicSection : Set G)).subgroupOf
        (Subgroup.normalizer (cyclicSection : Set G))) := by
  let : IsCyclic cyclicSection := hcyclic
  have htwo := cyclic_two_group_automorphisms_isPGroup cyclicSection
    (sylow.isPGroup'.to_le hle)
  have hrange := htwo.to_subgroup cyclicSection.normalizerMonoidHom.range
  have hkernel := hrange.of_equiv
    (QuotientGroup.quotientKerEquivRange cyclicSection.normalizerMonoidHom).symm
  exact hkernel.of_equiv (QuotientGroup.quotientMulEquivOfEq
    cyclicSection.normalizerMonoidHom_ker)

theorem exists_cyclic_two_section_normalizer_complement {G : Type*}
    [Group G] [Finite G] (sylow : Sylow 2 G) (cyclicSection : Subgroup G)
    (hle : cyclicSection ≤ (sylow : Subgroup G)) (hcyclic : IsCyclic cyclicSection)
    (hne : cyclicSection ≠ ⊥)
    (hnormalizes : (sylow : Subgroup G) ≤ Subgroup.normalizer (cyclicSection : Set G))
    (hcentralizer : IsCyclic
      ((Subgroup.centralizer (cyclicSection : Set G)).subgroupOf (sylow : Subgroup G))) :
    ∃ kernel : Subgroup (Subgroup.normalizer (cyclicSection : Set G)),
      kernel.Normal ∧ Odd (Nat.card kernel) ∧
      kernel ≤ (Subgroup.centralizer (cyclicSection : Set G)).subgroupOf
        (Subgroup.normalizer (cyclicSection : Set G)) ∧
      kernel.IsComplement' ((sylow : Subgroup G).subgroupOf
        (Subgroup.normalizer (cyclicSection : Set G))) ∧
      (kernel.subgroupOf ((Subgroup.centralizer (cyclicSection : Set G)).subgroupOf
        (Subgroup.normalizer (cyclicSection : Set G)))).Characteristic := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let normalizer := Subgroup.normalizer (cyclicSection : Set G)
  let centralizer := Subgroup.centralizer (cyclicSection : Set G)
  let localCentralizer := centralizer.subgroupOf normalizer
  let localSylow := sylow.subtype hnormalizes
  let : IsCyclic cyclicSection := hcyclic
  let : IsCyclic (centralizer.subgroupOf (sylow : Subgroup G)) := hcentralizer
  have hlocalCyclic : IsCyclic
      ((localSylow : Subgroup normalizer).subgroupOf localCentralizer) := by
    let inclusion : ((localSylow : Subgroup normalizer).subgroupOf localCentralizer) →*
        (centralizer.subgroupOf (sylow : Subgroup G)) :=
      { toFun := fun member => ⟨⟨member.val.val.val, member.property⟩, member.val.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply isCyclic_of_injective inclusion
    intro first second hequal
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun member => member.val.val) hequal
  have hsectionCentralizer : cyclicSection ≤ centralizer :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hevenSection : Even (Nat.card cyclicSection) := by
    let : Nontrivial cyclicSection := (Subgroup.nontrivial_iff_ne_bot cyclicSection).mpr hne
    have hcardne : Nat.card cyclicSection ≠ 1 := by
      intro hone
      have hsubsingleton := (Nat.card_eq_one_iff_unique.mp hone).1
      obtain ⟨first, second, hnePair⟩ := exists_pair_ne cyclicSection
      exact hnePair (hsubsingleton.elim first second)
    have htwo := sylow.isPGroup'.to_le hle
    exact even_iff_two_dvd.mpr (htwo.card_eq_or_dvd.resolve_left hcardne)
  have hevenCentralizer : Even (Nat.card localCentralizer) := by
    have heven := even_iff_two_dvd.mpr
      ((even_iff_two_dvd.mp hevenSection).trans
        (Subgroup.card_dvd_of_le hsectionCentralizer))
    have hcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (cyclicSection : Set G))).toEquiv
    exact hcard ▸ heven
  obtain ⟨kernel, hnormal, hodd, hkernelLe, hcomplement, hcharacteristic, _, _⟩ :=
    cyclic_sylow_centralizer_odd_normal_complement localSylow localCentralizer
      hlocalCyclic hevenCentralizer
      (cyclic_two_section_normalizer_quotient_isPGroup sylow cyclicSection hle hcyclic)
  exact ⟨kernel, hnormal, hodd, hkernelLe, hcomplement, hcharacteristic⟩

@[expose] noncomputable def normalComplementProjection {G : Type*} [Group G]
    {kernel complement : Subgroup G} [kernel.Normal]
    (hcomplement : kernel.IsComplement' complement) : G →* complement :=
  hcomplement.symm.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' kernel)

theorem normalComplementProjection_subtype {G : Type*} [Group G]
    {kernel complement : Subgroup G} [kernel.Normal]
    (hcomplement : kernel.IsComplement' complement) (element : complement) :
    normalComplementProjection hcomplement element = element := by
  apply hcomplement.symm.QuotientMulEquiv.symm.injective
  change hcomplement.symm.QuotientMulEquiv.symm
    (hcomplement.symm.QuotientMulEquiv (QuotientGroup.mk' kernel element)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem normalComplementProjection_surjective {G : Type*} [Group G]
    {kernel complement : Subgroup G} [kernel.Normal]
    (hcomplement : kernel.IsComplement' complement) :
    Function.Surjective (normalComplementProjection hcomplement) := by
  intro element
  exact ⟨element, normalComplementProjection_subtype hcomplement element⟩

theorem normalComplementProjection_ker {G : Type*} [Group G]
    {kernel complement : Subgroup G} [kernel.Normal]
    (hcomplement : kernel.IsComplement' complement) :
    (normalComplementProjection hcomplement).ker = kernel := by
  rw [normalComplementProjection, MonoidHom.ker_comp_of_injective _ _
    hcomplement.symm.QuotientMulEquiv.injective, QuotientGroup.ker_mk']

theorem normalComplementProjection_unique {G : Type*} [Group G]
    {kernel complement : Subgroup G} [kernel.Normal]
    (hcomplement : kernel.IsComplement' complement) (homomorphism : G →* complement)
    (hkernel : kernel ≤ homomorphism.ker)
    (hidentity : ∀ element : complement, homomorphism element = element) :
    homomorphism = normalComplementProjection hcomplement := by
  ext element
  have hmember : element ∈ kernel ⊔ complement := by rw [hcomplement.sup_eq_top]; trivial
  obtain ⟨kernelMember, hkernelMember, complementMember, hcomplementMember, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hmember
  rw [map_mul, map_mul, hkernel hkernelMember]
  have hprojectionKernel : normalComplementProjection hcomplement kernelMember = 1 := by
    change kernelMember ∈ (normalComplementProjection hcomplement).ker
    rw [normalComplementProjection_ker]
    exact hkernelMember
  rw [hprojectionKernel, one_mul, one_mul,
    hidentity ⟨complementMember, hcomplementMember⟩,
    normalComplementProjection_subtype hcomplement ⟨complementMember, hcomplementMember⟩]

end CFSG.TwoRankLowerBound.Helpers
