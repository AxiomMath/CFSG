module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G]

theorem pCore_eq_sSup (prime : ℕ) :
    pCore prime G = sSup {normalGroup : Subgroup G |
      normalGroup.Normal ∧ IsPGroup prime normalGroup} :=
  rfl

theorem pCore_normal (prime : ℕ) : (pCore prime G).Normal := by
  rw [pCore_eq_sSup]
  exact Subgroup.sSup_normal _ fun _ hnormalGroup => hnormalGroup.1

theorem pCore_isPGroup (prime : ℕ) : IsPGroup prime (pCore prime G) := by
  rw [pCore_eq_sSup]
  exact Sylow.sSup_of_normal _ (fun _ hnormalGroup => hnormalGroup.2)
    (fun _ hnormalGroup => hnormalGroup.1)

theorem normal_pGroup_le_pCore (prime : ℕ) (normalGroup : Subgroup G)
    (hnormal : normalGroup.Normal) (hpGroup : IsPGroup prime normalGroup) :
    normalGroup ≤ pCore prime G := by
  rw [pCore_eq_sSup]
  exact le_sSup ⟨hnormal, hpGroup⟩

theorem pCore_map_le (prime : ℕ) (automorphism : MulAut G) :
    (pCore prime G).map automorphism.toMonoidHom ≤ pCore prime G := by
  apply Subgroup.map_le_iff_le_comap.mpr
  conv_lhs => rw [pCore_eq_sSup]
  apply sSup_le
  rintro normalGroup ⟨hnormal, hpGroup⟩
  apply Subgroup.map_le_iff_le_comap.mp
  exact normal_pGroup_le_pCore prime (normalGroup.map automorphism.toMonoidHom)
    (hnormal.map automorphism.toMonoidHom automorphism.surjective)
    (hpGroup.map automorphism.toMonoidHom)

theorem pCore_characteristic (prime : ℕ) : (pCore prime G).Characteristic := by
  exact Subgroup.characteristic_iff_map_le.mpr (pCore_map_le prime)

theorem pCore_map_eq (prime : ℕ) (automorphism : MulAut G) :
    (pCore prime G).map automorphism.toMonoidHom = pCore prime G := by
  exact Subgroup.characteristic_iff_map_eq.mp (pCore_characteristic prime) automorphism

theorem pCoreOf_le (prime : ℕ) (localGroup : Subgroup G) : pCoreOf prime localGroup ≤ localGroup := by
  exact (Subgroup.map_le_range localGroup.subtype (pCore prime localGroup)).trans
    (le_of_eq localGroup.subtype_range)

theorem pCoreOf_subgroupOf (prime : ℕ) (localGroup : Subgroup G) :
    (pCoreOf prime localGroup).subgroupOf localGroup = pCore prime localGroup := by
  exact Subgroup.comap_map_eq_self_of_injective localGroup.subtype_injective _

theorem pCoreOf_normal (prime : ℕ) (localGroup : Subgroup G) :
    ((pCoreOf prime localGroup).subgroupOf localGroup).Normal := by
  rw [pCoreOf_subgroupOf]
  exact pCore_normal prime

theorem pCoreOf_isPGroup (prime : ℕ) (localGroup : Subgroup G) :
    IsPGroup prime (pCoreOf prime localGroup) := by
  exact (pCore_isPGroup prime).map localGroup.subtype

theorem localGroup_le_normalizer_pCoreOf (prime : ℕ) (localGroup : Subgroup G) :
    localGroup ≤ Subgroup.normalizer (pCoreOf prime localGroup : Set G) := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le prime localGroup)).mp
    (pCoreOf_normal prime localGroup)

theorem normal_pGroup_le_pCoreOf (prime : ℕ) (normalGroup localGroup : Subgroup G)
    (hinclusion : normalGroup ≤ localGroup)
    (hnormal : (normalGroup.subgroupOf localGroup).Normal)
    (hpGroup : IsPGroup prime normalGroup) : normalGroup ≤ pCoreOf prime localGroup := by
  have hrestricted : IsPGroup prime (normalGroup.subgroupOf localGroup) :=
    hpGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hinclusion).symm
  have hinternal := normal_pGroup_le_pCore prime (normalGroup.subgroupOf localGroup)
    hnormal hrestricted
  have himage := Subgroup.map_mono (f := localGroup.subtype) hinternal
  rwa [Subgroup.map_subgroupOf_eq_of_le hinclusion] at himage

theorem twoLocal_witness_le_pCoreOf (twoGroup localGroup : Subgroup G)
    (htwoGroup : IsPGroup 2 twoGroup)
    (hnormalizer : localGroup = Subgroup.normalizer (twoGroup : Set G)) :
    twoGroup ≤ pCoreOf 2 localGroup := by
  apply normal_pGroup_le_pCoreOf 2 twoGroup localGroup
  · rw [hnormalizer]
    exact Subgroup.le_normalizer
  · rw [hnormalizer]
    infer_instance
  · exact htwoGroup

theorem twoLocal_pCoreOf_ne_bot (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup) :
    pCoreOf 2 localGroup ≠ ⊥ := by
  obtain ⟨twoGroup, hnontrivial, htwoGroup, hnormalizer⟩ := hlocal
  intro htrivial
  have hcontained := twoLocal_witness_le_pCoreOf twoGroup localGroup htwoGroup hnormalizer
  rw [htrivial] at hcontained
  exact hnontrivial (le_bot_iff.mp hcontained)

theorem normalizer_pCoreOf_isTwoLocal (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup) :
    IsTwoLocal (Subgroup.normalizer (pCoreOf 2 localGroup : Set G)) := by
  exact ⟨pCoreOf 2 localGroup, twoLocal_pCoreOf_ne_bot localGroup hlocal,
    pCoreOf_isPGroup 2 localGroup, rfl⟩

theorem maxTwoLocal_eq_normalizer_pCoreOf (localGroup : Subgroup G)
    (hmaximal : rankThreeIsMaxTwoLocal localGroup) :
    localGroup = Subgroup.normalizer (pCoreOf 2 localGroup : Set G) := by
  exact (hmaximal.2 _ (normalizer_pCoreOf_isTwoLocal localGroup hmaximal.1)
    (localGroup_le_normalizer_pCoreOf 2 localGroup)).symm

theorem normalizer_localGroup_le_normalizer_pCoreOf (prime : ℕ) (localGroup : Subgroup G) :
    Subgroup.normalizer (localGroup : Set G) ≤
      Subgroup.normalizer (pCoreOf prime localGroup : Set G) := by
  intro normalizingElement hnormalizing
  let internalAutomorphism := localGroup.normalizerMonoidHom ⟨normalizingElement, hnormalizing⟩
  have hpreserved := pCore_map_le prime internalAutomorphism
  apply Subgroup.mem_normalizer_iff.mpr
  intro element
  constructor
  · rintro ⟨internalElement, hcore, rfl⟩
    have himage : internalAutomorphism internalElement ∈ pCore prime localGroup :=
      hpreserved (Subgroup.mem_map_of_mem internalAutomorphism.toMonoidHom hcore)
    have hcoercion := Subgroup.normalizerMonoidHom_apply_apply_coe localGroup
      (⟨normalizingElement, hnormalizing⟩ : Subgroup.normalizer (localGroup : Set G)) internalElement
    exact Subgroup.mem_map.mpr ⟨internalAutomorphism internalElement, himage, hcoercion⟩
  · intro hconjugate
    obtain ⟨internalImage, hcore, hcoercion⟩ := hconjugate
    have hinverse := pCore_map_le prime internalAutomorphism.symm
    have hsource : internalAutomorphism.symm internalImage ∈ pCore prime localGroup :=
      hinverse (Subgroup.mem_map_of_mem internalAutomorphism.symm.toMonoidHom hcore)
    apply Subgroup.mem_map.mpr
    refine ⟨internalAutomorphism.symm internalImage, hsource, ?_⟩
    have hinternal := Subgroup.normalizerMonoidHom_apply_apply_coe localGroup
      (⟨normalizingElement, hnormalizing⟩ : Subgroup.normalizer (localGroup : Set G))
      (internalAutomorphism.symm internalImage)
    have hinternalImage : internalAutomorphism (internalAutomorphism.symm internalImage) =
        internalImage := internalAutomorphism.apply_symm_apply internalImage
    change internalAutomorphism (internalAutomorphism.symm internalImage) = _ at hinternalImage
    have hambient := congrArg (fun internalElement : localGroup => (internalElement : G)) hinternalImage
    change (internalImage : G) = normalizingElement * element * normalizingElement⁻¹ at hcoercion
    rw [hinternal, hcoercion] at hambient
    exact mul_left_cancel (mul_right_cancel hambient)

theorem maxTwoLocal_self_normalizing (localGroup : Subgroup G)
    (hmaximal : rankThreeIsMaxTwoLocal localGroup) :
    Subgroup.normalizer (localGroup : Set G) = localGroup := by
  apply le_antisymm
  · exact (normalizer_localGroup_le_normalizer_pCoreOf 2 localGroup).trans
      (le_of_eq (maxTwoLocal_eq_normalizer_pCoreOf localGroup hmaximal).symm)
  · exact Subgroup.le_normalizer

theorem charTwo_local_centralizing_subgroup_le_core (hchar : IsCharTwoType G)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup) (centralizingGroup : Subgroup G)
    (hinclusion : centralizingGroup ≤ localGroup)
    (hcentralizing : centralizingGroup ≤ Subgroup.centralizer (pCoreOf 2 localGroup : Set G)) :
    centralizingGroup ≤ pCoreOf 2 localGroup := by
  exact (le_inf hinclusion hcentralizing).trans (hchar localGroup hlocal)

theorem charTwo_odd_pGroup_centralizer_eq_bot (hchar : IsCharTwoType G)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (oddGroup : Subgroup G) (hpGroup : IsPGroup prime oddGroup)
    (hinclusion : oddGroup ≤ localGroup) :
    oddGroup ⊓ Subgroup.centralizer (pCoreOf 2 localGroup : Set G) = ⊥ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisjoint := IsPGroup.disjoint_of_ne prime 2 hodd oddGroup (pCoreOf 2 localGroup)
    hpGroup (pCoreOf_isPGroup 2 localGroup)
  apply le_bot_iff.mp
  have hcontained : oddGroup ⊓ Subgroup.centralizer (pCoreOf 2 localGroup : Set G) ≤
      pCoreOf 2 localGroup :=
    charTwo_local_centralizing_subgroup_le_core hchar localGroup hlocal _
      (inf_le_left.trans hinclusion) inf_le_right
  exact (le_inf inf_le_left hcontained).trans (le_of_eq hdisjoint.eq_bot)

theorem charTwo_odd_pGroup_centralizing_core_eq_bot (hchar : IsCharTwoType G)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (oddGroup : Subgroup G) (hpGroup : IsPGroup prime oddGroup)
    (hinclusion : oddGroup ≤ localGroup)
    (hcentralizing : oddGroup ≤ Subgroup.centralizer (pCoreOf 2 localGroup : Set G)) :
    oddGroup = ⊥ := by
  have htrivial := charTwo_odd_pGroup_centralizer_eq_bot hchar localGroup hlocal prime hprime hodd
    oddGroup hpGroup hinclusion
  rwa [inf_eq_left.mpr hcentralizing] at htrivial

theorem charTwo_normal_odd_pGroup_eq_bot (hchar : IsCharTwoType G)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (oddGroup : Subgroup G) (hpGroup : IsPGroup prime oddGroup)
    (hinclusion : oddGroup ≤ localGroup)
    (hnormal : (oddGroup.subgroupOf localGroup).Normal) : oddGroup = ⊥ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrestricted : IsPGroup prime (oddGroup.subgroupOf localGroup) :=
    hpGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hinclusion).symm
  have hdisjoint := IsPGroup.disjoint_of_ne prime 2 hodd
    (oddGroup.subgroupOf localGroup) (pCore 2 localGroup) hrestricted (pCore_isPGroup 2)
  apply charTwo_odd_pGroup_centralizing_core_eq_bot hchar localGroup hlocal prime hprime hodd
    oddGroup hpGroup hinclusion
  intro oddElement hoddElement
  apply Subgroup.mem_centralizer_iff.mpr
  rintro coreElement ⟨internalCore, hcore, rfl⟩
  have hcommute := Subgroup.commute_of_normal_of_disjoint
    (oddGroup.subgroupOf localGroup) (pCore 2 localGroup) hnormal (pCore_normal 2) hdisjoint
    (⟨oddElement, hinclusion hoddElement⟩ : localGroup) internalCore hoddElement hcore
  exact (congrArg (fun internalElement : localGroup => (internalElement : G)) hcommute.eq).symm

theorem charTwo_odd_pCoreOf_eq_bot (hchar : IsCharTwoType G)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2) :
    pCoreOf prime localGroup = ⊥ := by
  exact charTwo_normal_odd_pGroup_eq_bot hchar localGroup hlocal prime hprime hodd
    (pCoreOf prime localGroup) (pCoreOf_isPGroup prime localGroup)
    (pCoreOf_le prime localGroup) (pCoreOf_normal prime localGroup)

theorem charTwo_odd_pCore_eq_bot (hchar : IsCharTwoType G)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2) :
    pCore prime localGroup = ⊥ := by
  have htrivial := charTwo_odd_pCoreOf_eq_bot hchar localGroup hlocal prime hprime hodd
  have hinternal := congrArg (fun subgroup : Subgroup G => subgroup.subgroupOf localGroup) htrivial
  simpa only [pCoreOf_subgroupOf, Subgroup.bot_subgroupOf] using hinternal

theorem charTwo_odd_rank_two_elementary_not_normal
    (hchar : IsCharTwoType G) (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (elementary : Subgroup G) (helementary : IsElemAbelian prime elementary)
    (hcard : Nat.card elementary = prime ^ 2) (hinclusion : elementary ≤ localGroup) :
    ¬ (elementary.subgroupOf localGroup).Normal := by
  intro hnormal
  have htrivial := charTwo_normal_odd_pGroup_eq_bot hchar localGroup hlocal prime hprime hodd
    elementary (elementary_isPGroup prime elementary helementary) hinclusion hnormal
  have hcardOne : Nat.card elementary = 1 := by
    rw [htrivial]
    exact Subgroup.card_bot
  have hlarge := Nat.one_lt_pow (by decide : (2 : ℕ) ≠ 0) hprime.one_lt
  omega

@[expose] noncomputable def localCoreConjugation (localGroup actingGroup : Subgroup G)
    (hinclusion : actingGroup ≤ localGroup) : actingGroup →* MulAut (pCoreOf 2 localGroup) :=
  (pCoreOf 2 localGroup).normalizerMonoidHom.comp
    (Subgroup.inclusion (hinclusion.trans (localGroup_le_normalizer_pCoreOf 2 localGroup)))

theorem localCoreConjugation_ker (localGroup actingGroup : Subgroup G)
    (hinclusion : actingGroup ≤ localGroup) :
    (localCoreConjugation localGroup actingGroup hinclusion).ker =
      (Subgroup.centralizer (pCoreOf 2 localGroup : Set G)).subgroupOf actingGroup := by
  ext actingElement
  change ((pCoreOf 2 localGroup).normalizerMonoidHom
    (Subgroup.inclusion
      (hinclusion.trans (localGroup_le_normalizer_pCoreOf 2 localGroup)) actingElement) = 1) ↔ _
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
  rfl

theorem charTwo_odd_pGroup_localCoreConjugation_injective (hchar : IsCharTwoType G)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (oddGroup : Subgroup G) (hpGroup : IsPGroup prime oddGroup)
    (hinclusion : oddGroup ≤ localGroup) :
    Function.Injective (localCoreConjugation localGroup oddGroup hinclusion) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [localCoreConjugation_ker]
  apply le_bot_iff.mp
  intro oddElement hcentralizing
  have hintersection : (oddElement : G) ∈
      oddGroup ⊓ Subgroup.centralizer (pCoreOf 2 localGroup : Set G) :=
    ⟨oddElement.property, hcentralizing⟩
  rw [charTwo_odd_pGroup_centralizer_eq_bot hchar localGroup hlocal prime hprime hodd
    oddGroup hpGroup hinclusion] at hintersection
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hintersection))

theorem charTwo_odd_pGroup_card_dvd_coreAut_card (hchar : IsCharTwoType G)
    (localGroup : Subgroup G) (hlocal : IsTwoLocal localGroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (oddGroup : Subgroup G) (hpGroup : IsPGroup prime oddGroup)
    (hinclusion : oddGroup ≤ localGroup) :
    Nat.card oddGroup ∣ Nat.card (MulAut (pCoreOf 2 localGroup)) := by
  exact Subgroup.card_dvd_of_injective
    (localCoreConjugation localGroup oddGroup hinclusion)
    (charTwo_odd_pGroup_localCoreConjugation_injective hchar localGroup hlocal prime hprime hodd
      oddGroup hpGroup hinclusion)

end CFSG.RankThreeCoreUniqueness.Helpers
