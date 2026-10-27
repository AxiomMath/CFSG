module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.Components
public import CFSG.LocalAnalysis.ComponentClassification.Layer

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoResidual

@[expose] noncomputable def subgroup (G : Type*) [Group G] : Subgroup G :=
  sSup {twoSubgroup : Subgroup G | IsPGroup 2 twoSubgroup}

theorem twoSubgroup_le {G : Type*} [Group G] (twoSubgroup : Subgroup G)
    (htwo : IsPGroup 2 twoSubgroup) : twoSubgroup ≤ subgroup G := le_sSup htwo

theorem map_le {G H : Type*} [Group G] [Group H] (homomorphism : G →* H) :
    (subgroup G).map homomorphism ≤ subgroup H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro twoSubgroup htwo
  exact Subgroup.map_le_iff_le_comap.mp
    (twoSubgroup_le (twoSubgroup.map homomorphism) (htwo.map homomorphism))

theorem equiv_invariant {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) :
    (subgroup G).map equivalence.toMonoidHom = subgroup H := by
  apply le_antisymm (map_le equivalence.toMonoidHom)
  intro element hmem
  have hinverse := map_le equivalence.symm.toMonoidHom
    (Subgroup.mem_map_of_mem equivalence.symm.toMonoidHom hmem)
  exact ⟨equivalence.symm element, hinverse, equivalence.apply_symm_apply element⟩

theorem characteristic (G : Type*) [Group G] : (subgroup G).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro automorphism
  exact equiv_invariant automorphism

theorem odd_index (G : Type*) [Group G] [Finite G] : Odd (subgroup G).index := by
  let sylow : Sylow 2 G := Classical.choice inferInstance
  have hle := twoSubgroup_le (sylow : Subgroup G) sylow.isPGroup'
  apply Nat.coprime_two_left.mp
  apply Nat.Coprime.of_dvd_right (Subgroup.index_dvd_of_le hle)
  exact Nat.prime_two.coprime_iff_not_dvd.mpr sylow.not_dvd_index

theorem normal_contains_of_odd_index {G : Type*} [Group G] [Finite G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] (hodd : Odd normalSubgroup.index) :
    subgroup G ≤ normalSubgroup := by
  apply sSup_le
  intro twoSubgroup htwo
  let quotient := QuotientGroup.mk' normalSubgroup
  have himageTwo : IsPGroup 2 (twoSubgroup.map quotient) := htwo.map quotient
  obtain ⟨exponent, hcard⟩ := himageTwo.exists_card_eq
  have hquotientOdd : Odd (Nat.card (G ⧸ normalSubgroup)) := hodd
  have hcoprime : (2 ^ exponent).Coprime (Nat.card (G ⧸ normalSubgroup)) :=
    hquotientOdd.coprime_two_left.pow_left exponent
  have himageCard : Nat.card (twoSubgroup.map quotient) = 1 := by
    apply Nat.eq_one_of_dvd_coprimes hcoprime
    · rw [hcard]
    · exact Subgroup.card_subgroup_dvd_card _
  have himageBot : twoSubgroup.map quotient = ⊥ := Subgroup.card_eq_one.mp himageCard
  have hkernel := twoSubgroup.map_eq_bot_iff.mp himageBot
  change twoSubgroup ≤ (QuotientGroup.mk' normalSubgroup).ker at hkernel
  simpa only [QuotientGroup.ker_mk'] using hkernel

theorem subnormal_contains_of_odd_index {G : Type*} [Group G] [Finite G]
    (subnormalSubgroup : Subgroup G) (hsubnormal : IsSubnormal subnormalSubgroup ⊤)
    (hodd : Odd subnormalSubgroup.index) : subgroup G ≤ subnormalSubgroup := by
  have hchain := Components.mathlib_subnormal_of_chain hsubnormal Subgroup.IsSubnormal.top
  clear hsubnormal
  induction hchain with
  | top => exact le_top
  | step lower upper hle hsubnormal hnormal hinduction =>
      have hupperOdd : Odd upper.index :=
        hodd.of_dvd_nat (Subgroup.index_dvd_of_le hle)
      have hupperContains := hinduction hupperOdd
      have hlowerOdd : Odd (lower.subgroupOf upper).index := by
        have hindex := Subgroup.index_map_subtype (lower.subgroupOf upper)
        rw [Subgroup.map_subgroupOf_eq_of_le hle] at hindex
        exact hodd.of_dvd_nat ⟨upper.index, hindex⟩
      let : (lower.subgroupOf upper).Normal := hnormal
      have hlocal := normal_contains_of_odd_index (lower.subgroupOf upper) hlowerOdd
      apply sSup_le
      intro twoSubgroup htwo
      have htwoUpper : twoSubgroup ≤ upper := (twoSubgroup_le _ htwo).trans hupperContains
      have hlocalTwo : IsPGroup 2 (twoSubgroup.subgroupOf upper) :=
        htwo.of_equiv (Subgroup.subgroupOfEquivOfLe htwoUpper).symm
      have hlocalContains := (twoSubgroup_le (twoSubgroup.subgroupOf upper) hlocalTwo).trans hlocal
      intro element hmem
      exact hlocalContains (show (⟨element, htwoUpper hmem⟩ : upper) ∈
        twoSubgroup.subgroupOf upper from hmem)

theorem image_of_surjective {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient) :
    (subgroup G).map quotient = subgroup H := by
  apply le_antisymm (map_le quotient)
  apply sSup_le
  intro twoSubgroup htwo
  let preimage := twoSubgroup.comap quotient
  let restriction : preimage →* twoSubgroup :=
    (quotient.domRestrict preimage).codRestrict twoSubgroup fun element => element.property
  have hrestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hlift⟩ := hsurjective element.val
    have hmem : lift ∈ preimage := by
      change quotient lift ∈ twoSubgroup
      rw [hlift]
      exact element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hlift⟩
  let sylow : Sylow 2 preimage := Classical.choice inferInstance
  have htopTwo : IsPGroup 2 (⊤ : Subgroup twoSubgroup) := htwo.to_subgroup ⊤
  have hnormal : (⊤ : Subgroup twoSubgroup).Normal := inferInstance
  let : (⊤ : Subgroup twoSubgroup).Normal := hnormal
  have himageTop : (sylow : Subgroup preimage).map restriction = ⊤ := by
    have hle := htopTwo.le_sylow_of_normal (sylow.mapSurjective hrestriction)
    rw [Sylow.coe_mapSurjective] at hle
    exact top_unique hle
  let ambientSylow := (sylow : Subgroup preimage).map preimage.subtype
  have hambientTwo : IsPGroup 2 ambientSylow := sylow.isPGroup'.map preimage.subtype
  have hambientLe := twoSubgroup_le ambientSylow hambientTwo
  intro element hmem
  have htarget : (⟨element, hmem⟩ : twoSubgroup) ∈ (sylow : Subgroup preimage).map restriction := by
    rw [himageTop]
    exact Subgroup.mem_top _
  obtain ⟨member, hmember, hvalue⟩ := Subgroup.mem_map.mp htarget
  exact ⟨member.val, hambientLe ⟨member, hmember, rfl⟩, congrArg Subtype.val hvalue⟩

theorem idempotent (G : Type*) [Group G] :
    (subgroup (subgroup G)).map (subgroup G).subtype = subgroup G := by
  apply le_antisymm (Subgroup.map_subtype_le _)
  apply sSup_le
  intro twoSubgroup htwo
  have hle := twoSubgroup_le twoSubgroup htwo
  have hlocalTwo : IsPGroup 2 (twoSubgroup.subgroupOf (subgroup G)) :=
    htwo.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hlocalLe := twoSubgroup_le (twoSubgroup.subgroupOf (subgroup G)) hlocalTwo
  intro element hmem
  exact ⟨⟨element, hle hmem⟩, hlocalLe hmem, rfl⟩

theorem odd_index_of_covering {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (coveringSubgroup : Subgroup G)
    (hcovering : Function.Surjective (quotient.domRestrict coveringSubgroup)) :
    Odd coveringSubgroup.index := by
  let : Finite H := Finite.of_surjective quotient hsurjective
  let restriction := quotient.domRestrict coveringSubgroup
  have hambientCard : Nat.card G = Nat.card H * Nat.card quotient.ker := by
    have hcard := quotient.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.liftEquiv quotient.ker hsurjective rfl).toEquiv] at hcard
    exact hcard
  have hcoverCard : Nat.card coveringSubgroup = Nat.card H * Nat.card restriction.ker := by
    have hcard := restriction.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.liftEquiv restriction.ker hcovering rfl).toEquiv] at hcard
    exact hcard
  have hmul : Nat.card H * (Nat.card restriction.ker * coveringSubgroup.index) =
      Nat.card H * Nat.card quotient.ker := by
    rw [← mul_assoc, ← hcoverCard, coveringSubgroup.card_mul_index, hambientCard]
  have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H)) hmul
  exact hoddKernel.of_dvd_nat ⟨Nat.card restriction.ker, by simpa only [mul_comm] using hcancel.symm⟩

theorem eq_of_subnormal_covering {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (coveringSubgroup : Subgroup G)
    (hsubnormal : IsSubnormal coveringSubgroup ⊤)
    (hgenerated : subgroup coveringSubgroup = ⊤)
    (hcovering : Function.Surjective (quotient.domRestrict coveringSubgroup)) :
    coveringSubgroup = subgroup G := by
  apply le_antisymm
  · have hmap := map_le coveringSubgroup.subtype
    rw [hgenerated] at hmap
    intro element hmem
    exact hmap ⟨⟨element, hmem⟩, Subgroup.mem_top _, rfl⟩
  · exact subnormal_contains_of_odd_index coveringSubgroup hsubnormal
      (odd_index_of_covering quotient hsurjective hoddKernel coveringSubgroup hcovering)

theorem normalizer_le_normalizer {G : Type*} [Group G] (overgroup : Subgroup G) :
    Subgroup.normalizer (overgroup : Set G) ≤
      Subgroup.normalizer ((subgroup overgroup).map overgroup.subtype : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor member hmember
  obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hactor
  let automorphism : overgroup ≃* overgroup :=
    ((MulAut.conj actor).subgroupMap overgroup).trans (MulEquiv.subgroupCongr hmap)
  have hresidual : automorphism lift ∈ subgroup overgroup := by
    rw [← equiv_invariant automorphism]
    exact Subgroup.mem_map_of_mem automorphism.toMonoidHom hlift
  exact Subgroup.mem_map.mpr ⟨automorphism lift, hresidual, rfl⟩

end CFSG.ComponentClassification.TwoResidual
