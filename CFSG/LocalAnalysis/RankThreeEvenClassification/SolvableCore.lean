module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoreTransport
public import CFSG.Assembly.Defs

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

@[expose] def IsSolvableNormalPrimeComplement {G : Type u} [Group G] (prime : ℕ)
    (subgroup : Subgroup G) : Prop :=
  subgroup.Normal ∧ Group.IsSolvable subgroup ∧ ¬prime ∣ Nat.card subgroup

@[expose] noncomputable def solvablePrimeComplementCore (G : Type u) [Group G] (prime : ℕ) :
    Subgroup G := sSup {subgroup : Subgroup G | IsSolvableNormalPrimeComplement prime subgroup}

theorem solvable_sup_of_normal {G : Type u} [Group G] (first second : Subgroup G)
    (hfirstNormal : first.Normal) (hsecondNormal : second.Normal)
    (hfirstSolvable : Group.IsSolvable first) (hsecondSolvable : Group.IsSolvable second) :
    Group.IsSolvable (first ⊔ second : Subgroup G) := by
  have : first.Normal := hfirstNormal
  have : second.Normal := hsecondNormal
  have : Group.IsSolvable first := hfirstSolvable
  have : Group.IsSolvable second := hsecondSolvable
  let equivalence := QuotientGroup.quotientInfEquivProdNormalizerQuotient first second
    (Subgroup.le_normalizer_of_normal : first ≤ Subgroup.normalizer (second : Set G))
  apply (Group.isSolvable_iff_subgroup_quotient (second.subgroupOf (first ⊔ second))).mpr
  constructor
  · let restriction := Subgroup.subgroupOfEquivOfLe (show second ≤ first ⊔ second from le_sup_right)
    exact Group.isSolvable_of_surjective (f := restriction.symm.toMonoidHom)
      restriction.symm.surjective
  · exact Group.isSolvable_of_surjective (f := equivalence.toMonoidHom) equivalence.surjective

theorem prime_not_dvd_card_sup_of_normal {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (first second : Subgroup G)
    (hfirstNormal : first.Normal) (hsecondNormal : second.Normal)
    (hfirst : ¬prime ∣ Nat.card first) (hsecond : ¬prime ∣ Nat.card second) :
    ¬prime ∣ Nat.card (first ⊔ second : Subgroup G) := by
  have : first.Normal := hfirstNormal
  have : second.Normal := hsecondNormal
  let equivalence := QuotientGroup.quotientInfEquivProdNormalizerQuotient first second
    (Subgroup.le_normalizer_of_normal : first ≤ Subgroup.normalizer (second : Set G))
  have hquotientCard : Nat.card ((first ⊔ second : Subgroup G) ⧸
      second.subgroupOf (first ⊔ second)) ∣
      Nat.card first := by
    rw [← Nat.card_congr equivalence.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  have hsectionCard : Nat.card (second.subgroupOf (first ⊔ second)) = Nat.card second :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show second ≤ first ⊔ second from
      le_sup_right)).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (second.subgroupOf (first ⊔ second)),
    hsectionCard, hprime.dvd_mul]
  exact fun hdiv => hdiv.elim (fun hquotient => hfirst (hquotient.trans hquotientCard)) hsecond

theorem solvableNormalPrimeComplement_sup {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (first second : Subgroup G)
    (hfirst : IsSolvableNormalPrimeComplement prime first)
    (hsecond : IsSolvableNormalPrimeComplement prime second) :
    IsSolvableNormalPrimeComplement prime (first ⊔ second) := by
  have : first.Normal := hfirst.1
  have : second.Normal := hsecond.1
  exact ⟨inferInstance, solvable_sup_of_normal first second hfirst.1 hsecond.1 hfirst.2.1 hsecond.2.1,
    prime_not_dvd_card_sup_of_normal prime hprime first second hfirst.1 hsecond.1
      hfirst.2.2 hsecond.2.2⟩

theorem solvableNormalPrimeComplement_bot {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) :
    IsSolvableNormalPrimeComplement prime (⊥ : Subgroup G) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  simpa only [Subgroup.card_bot] using hprime.not_dvd_one

theorem solvablePrimeComplementCore_properties (G : Type u) [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) :
    IsSolvableNormalPrimeComplement prime (solvablePrimeComplementCore G prime) := by
  obtain ⟨maximalSubgroup, _, hmaximal⟩ := Finite.exists_le_maximal
    (solvableNormalPrimeComplement_bot (G := G) prime hprime)
  have hgreatest : ∀ subgroup : Subgroup G, IsSolvableNormalPrimeComplement prime subgroup →
      subgroup ≤ maximalSubgroup := by
    intro subgroup hsubgroup
    have heq := hmaximal.eq_of_le
      (solvableNormalPrimeComplement_sup prime hprime maximalSubgroup subgroup
        hmaximal.1 hsubgroup) le_sup_left
    exact heq.symm ▸ le_sup_right
  have heq : solvablePrimeComplementCore G prime = maximalSubgroup := by
    apply le_antisymm (sSup_le hgreatest)
    exact le_sSup hmaximal.1
  exact heq.symm ▸ hmaximal.1

theorem le_solvablePrimeComplementCore {G : Type u} [Group G]
    (prime : ℕ) (subgroup : Subgroup G) (hnormal : subgroup.Normal)
    (hsolvable : Group.IsSolvable subgroup) (hprimeComplement : ¬prime ∣ Nat.card subgroup) :
    subgroup ≤ solvablePrimeComplementCore G prime := by
  exact le_sSup ⟨hnormal, hsolvable, hprimeComplement⟩

theorem solvablePrimeComplementCore_map_le {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (equivalence : G ≃* otherGroup) :
    (solvablePrimeComplementCore G prime).map equivalence.toMonoidHom ≤
      solvablePrimeComplementCore otherGroup prime := by
  obtain ⟨hnormal, hsolvable, hprimeComplement⟩ := solvablePrimeComplementCore_properties G prime hprime
  have : Group.IsSolvable (solvablePrimeComplementCore G prime) := hsolvable
  apply le_solvablePrimeComplementCore prime
  · exact hnormal.map equivalence.toMonoidHom equivalence.surjective
  · exact Group.isSolvable_of_surjective
      (f := (equivalence.subgroupMap (solvablePrimeComplementCore G prime)).toMonoidHom)
      (equivalence.subgroupMap (solvablePrimeComplementCore G prime)).surjective
  · simpa only [Subgroup.card_map_of_injective (f := equivalence.toMonoidHom)
      equivalence.injective] using hprimeComplement

theorem solvablePrimeComplementCore_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (equivalence : G ≃* otherGroup) :
    (solvablePrimeComplementCore G prime).map equivalence.toMonoidHom =
      solvablePrimeComplementCore otherGroup prime := by
  apply le_antisymm (solvablePrimeComplementCore_map_le prime hprime equivalence)
  apply (Subgroup.map_le_map_iff_of_injective
    (f := equivalence.symm.toMonoidHom) equivalence.symm.injective).mp
  rw [subgroup_map_equiv_symm]
  exact solvablePrimeComplementCore_map_le prime hprime equivalence.symm

theorem solvablePrimeComplementCore_characteristic (G : Type u) [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) : (solvablePrimeComplementCore G prime).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro equivalence
  exact solvablePrimeComplementCore_map_equiv prime hprime equivalence

theorem solvablePrimeComplementCore_eq_bot_of_simple (G : Type u) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ first second : G, first * second ≠ second * first)
    (prime : ℕ) (hprime : prime.Prime) : solvablePrimeComplementCore G prime = ⊥ := by
  obtain ⟨hnormal, hsolvable, _⟩ := solvablePrimeComplementCore_properties G prime hprime
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · have : Group.IsSolvable (solvablePrimeComplementCore G prime) := hsolvable
    have hgroupSolvable : Group.IsSolvable G := by
      have : Group.IsSolvable (⊤ : Subgroup G) := htop ▸ hsolvable
      exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := G)).toMonoidHom)
        (Subgroup.topEquiv (G := G)).surjective
    obtain ⟨first, second, hne⟩ := hnonab
    exact False.elim (hne (IsSimpleGroup.comm_iff_isSolvable.mpr hgroupSolvable first second))

end CFSG.RankThreeEvenClassification.Helpers
