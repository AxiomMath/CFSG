module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableCore

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

@[expose] noncomputable def solvableRadical (G : Type u) [Group G] : Subgroup G :=
  sSup {subgroup : Subgroup G | subgroup.Normal ∧ Group.IsSolvable subgroup}

@[expose] noncomputable def primeComplementCore (G : Type u) [Group G] (prime : ℕ) : Subgroup G :=
  sSup {subgroup : Subgroup G | subgroup.Normal ∧ ¬prime ∣ Nat.card subgroup}

@[expose] noncomputable def aschbacherTheta (G : Type u) [Group G] (prime : ℕ) : Subgroup G :=
  (primeComplementCore (solvableRadical G) prime).map (solvableRadical G).subtype

theorem solvableRadical_properties (G : Type u) [Group G] [Finite G] :
    (solvableRadical G).Normal ∧ Group.IsSolvable (solvableRadical G) := by
  have hbot : (⊥ : Subgroup G).Normal ∧ Group.IsSolvable (⊥ : Subgroup G) :=
    ⟨inferInstance, inferInstance⟩
  obtain ⟨maximalSubgroup, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun subgroup : Subgroup G => subgroup.Normal ∧ Group.IsSolvable subgroup) hbot
  have hgreatest : ∀ subgroup : Subgroup G, subgroup.Normal ∧ Group.IsSolvable subgroup →
      subgroup ≤ maximalSubgroup := by
    rintro subgroup ⟨hnormal, hsolvable⟩
    have : maximalSubgroup.Normal := hmaximal.1.1
    have : subgroup.Normal := hnormal
    have heq := hmaximal.eq_of_le ⟨inferInstance,
      solvable_sup_of_normal maximalSubgroup subgroup hmaximal.1.1 hnormal
        hmaximal.1.2 hsolvable⟩ le_sup_left
    exact heq.symm ▸ le_sup_right
  have heq : solvableRadical G = maximalSubgroup :=
    le_antisymm (sSup_le hgreatest) (le_sSup hmaximal.1)
  exact heq.symm ▸ hmaximal.1

theorem le_solvableRadical {G : Type u} [Group G] (subgroup : Subgroup G)
    (hnormal : subgroup.Normal) (hsolvable : Group.IsSolvable subgroup) :
    subgroup ≤ solvableRadical G := le_sSup ⟨hnormal, hsolvable⟩

theorem primeComplementCore_properties (G : Type u) [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) :
    (primeComplementCore G prime).Normal ∧ ¬prime ∣ Nat.card (primeComplementCore G prime) := by
  have hbot : (⊥ : Subgroup G).Normal ∧ ¬prime ∣ Nat.card (⊥ : Subgroup G) :=
    ⟨inferInstance, by simpa only [Subgroup.card_bot] using hprime.not_dvd_one⟩
  obtain ⟨maximalSubgroup, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun subgroup : Subgroup G => subgroup.Normal ∧ ¬prime ∣ Nat.card subgroup) hbot
  have hgreatest : ∀ subgroup : Subgroup G, subgroup.Normal ∧ ¬prime ∣ Nat.card subgroup →
      subgroup ≤ maximalSubgroup := by
    rintro subgroup ⟨hnormal, hcomplement⟩
    have : maximalSubgroup.Normal := hmaximal.1.1
    have : subgroup.Normal := hnormal
    have heq := hmaximal.eq_of_le ⟨inferInstance,
      prime_not_dvd_card_sup_of_normal prime hprime maximalSubgroup subgroup
        hmaximal.1.1 hnormal hmaximal.1.2 hcomplement⟩ le_sup_left
    exact heq.symm ▸ le_sup_right
  have heq : primeComplementCore G prime = maximalSubgroup :=
    le_antisymm (sSup_le hgreatest) (le_sSup hmaximal.1)
  exact heq.symm ▸ hmaximal.1

theorem le_primeComplementCore {G : Type u} [Group G] (prime : ℕ) (subgroup : Subgroup G)
    (hnormal : subgroup.Normal) (hcomplement : ¬prime ∣ Nat.card subgroup) :
    subgroup ≤ primeComplementCore G prime := le_sSup ⟨hnormal, hcomplement⟩

theorem primeComplementCore_map_le {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (equivalence : G ≃* otherGroup) :
    (primeComplementCore G prime).map equivalence.toMonoidHom ≤ primeComplementCore otherGroup prime := by
  obtain ⟨hnormal, hcomplement⟩ := primeComplementCore_properties G prime hprime
  apply le_primeComplementCore prime
  · exact hnormal.map equivalence.toMonoidHom equivalence.surjective
  · simpa only [Subgroup.card_map_of_injective (f := equivalence.toMonoidHom)
      equivalence.injective] using hcomplement

theorem primeComplementCore_map_equiv {G : Type u} {otherGroup : Type v}
    [Group G] [Group otherGroup] [Finite G] [Finite otherGroup]
    (prime : ℕ) (hprime : prime.Prime) (equivalence : G ≃* otherGroup) :
    (primeComplementCore G prime).map equivalence.toMonoidHom = primeComplementCore otherGroup prime := by
  apply le_antisymm (primeComplementCore_map_le prime hprime equivalence)
  apply (Subgroup.map_le_map_iff_of_injective
    (f := equivalence.symm.toMonoidHom) equivalence.symm.injective).mp
  rw [subgroup_map_equiv_symm]
  exact primeComplementCore_map_le prime hprime equivalence.symm

theorem primeComplementCore_characteristic (G : Type u) [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) : (primeComplementCore G prime).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro equivalence
  exact primeComplementCore_map_equiv prime hprime equivalence

theorem aschbacherTheta_properties (G : Type u) [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) :
    IsSolvableNormalPrimeComplement prime (aschbacherTheta G prime) := by
  obtain ⟨hradicalNormal, hradicalSolvable⟩ := solvableRadical_properties G
  have : (solvableRadical G).Normal := hradicalNormal
  have : Group.IsSolvable (solvableRadical G) := hradicalSolvable
  have : (primeComplementCore (solvableRadical G) prime).Characteristic :=
    primeComplementCore_characteristic (solvableRadical G) prime hprime
  constructor
  · exact ConjAct.normal_of_characteristic_of_normal
  constructor
  · let equivalence := (primeComplementCore (solvableRadical G) prime).equivMapOfInjective
      (solvableRadical G).subtype (solvableRadical G).subtype_injective
    exact Group.isSolvable_of_surjective (f := equivalence.toMonoidHom) equivalence.surjective
  · obtain ⟨_, hcomplement⟩ := primeComplementCore_properties (solvableRadical G) prime hprime
    simpa only [aschbacherTheta,
      Subgroup.card_map_of_injective (solvableRadical G).subtype_injective] using hcomplement

theorem aschbacherTheta_eq_solvablePrimeComplementCore (G : Type u) [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) :
    aschbacherTheta G prime = solvablePrimeComplementCore G prime := by
  apply le_antisymm
  · obtain ⟨hnormal, hsolvable, hcomplement⟩ := aschbacherTheta_properties G prime hprime
    exact le_solvablePrimeComplementCore prime (aschbacherTheta G prime) hnormal hsolvable hcomplement
  · obtain ⟨hnormal, hsolvable, hcomplement⟩ := solvablePrimeComplementCore_properties G prime hprime
    have : (solvablePrimeComplementCore G prime).Normal := hnormal
    have hle := le_solvableRadical (solvablePrimeComplementCore G prime) hnormal hsolvable
    have hrestricted : ¬prime ∣ Nat.card ((solvablePrimeComplementCore G prime).subgroupOf
        (solvableRadical G)) := by
      simpa only [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] using hcomplement
    have hcore := le_primeComplementCore prime
      ((solvablePrimeComplementCore G prime).subgroupOf (solvableRadical G))
      inferInstance hrestricted
    have hmap := Subgroup.map_mono (f := (solvableRadical G).subtype) hcore
    simpa only [Subgroup.map_subgroupOf_eq_of_le hle, aschbacherTheta] using hmap

theorem aschbacherTheta_characteristic (G : Type u) [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) : (aschbacherTheta G prime).Characteristic := by
  rw [aschbacherTheta_eq_solvablePrimeComplementCore G prime hprime]
  exact solvablePrimeComplementCore_characteristic G prime hprime

end CFSG.RankThreeEvenClassification.Helpers
