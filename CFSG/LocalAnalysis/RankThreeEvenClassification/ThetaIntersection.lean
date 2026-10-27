module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableCore

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] noncomputable def thetaCoreOf {G : Type u} [Group G] (prime : ℕ) (subgroup : Subgroup G) :
    Subgroup G := (solvablePrimeComplementCore subgroup prime).map subgroup.subtype

theorem thetaCoreOf_le {G : Type u} [Group G] (prime : ℕ) (subgroup : Subgroup G) :
    thetaCoreOf prime subgroup ≤ subgroup := Subgroup.map_subtype_le _

theorem thetaCoreOf_solvable {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) :
    Group.IsSolvable (thetaCoreOf prime subgroup) := by
  have : Group.IsSolvable (solvablePrimeComplementCore subgroup prime) :=
    (solvablePrimeComplementCore_properties subgroup prime hprime).2.1
  let equivalence := (solvablePrimeComplementCore subgroup prime).equivMapOfInjective
    subgroup.subtype subgroup.subtype_injective
  exact Group.isSolvable_of_surjective (f := equivalence.toMonoidHom) equivalence.surjective

theorem thetaCoreOf_prime_complement {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) :
    ¬prime ∣ Nat.card (thetaCoreOf prime subgroup) := by
  have hcomplement := (solvablePrimeComplementCore_properties subgroup prime hprime).2.2
  simpa only [thetaCoreOf, Subgroup.card_map_of_injective subgroup.subtype_injective]
    using hcomplement

theorem thetaCoreOf_normal_of_normal {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) (hnormal : subgroup.Normal) :
    (thetaCoreOf prime subgroup).Normal := by
  have : subgroup.Normal := hnormal
  have : (solvablePrimeComplementCore subgroup prime).Characteristic :=
    solvablePrimeComplementCore_characteristic subgroup prime hprime
  exact ConjAct.normal_of_characteristic_of_normal

theorem thetaCoreOf_subgroupOf {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (smaller larger : Subgroup G) (hle : smaller ≤ larger) :
    (thetaCoreOf prime smaller).subgroupOf larger = thetaCoreOf prime (smaller.subgroupOf larger) := by
  apply Subgroup.map_injective larger.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((thetaCoreOf_le prime smaller).trans hle)]
  unfold thetaCoreOf
  rw [Subgroup.map_map]
  have hcomposition : larger.subtype.comp (smaller.subgroupOf larger).subtype =
      smaller.subtype.comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom := by
    ext element
    rfl
  rw [hcomposition, ← Subgroup.map_map, solvablePrimeComplementCore_map_equiv prime hprime]

theorem normal_solvable_primeComplement_le_thetaCoreOf {G : Type u} [Group G]
    (prime : ℕ) (smaller larger : Subgroup G) (hle : smaller ≤ larger)
    (hnormal : (smaller.subgroupOf larger).Normal) (hsolvable : Group.IsSolvable smaller)
    (hcomplement : ¬prime ∣ Nat.card smaller) : smaller ≤ thetaCoreOf prime larger := by
  have : Group.IsSolvable smaller := hsolvable
  let equivalence := Subgroup.subgroupOfEquivOfLe hle
  have hrestrictedSolvable : Group.IsSolvable (smaller.subgroupOf larger) :=
    Group.isSolvable_of_surjective (f := equivalence.symm.toMonoidHom) equivalence.symm.surjective
  have hrestrictedComplement : ¬prime ∣ Nat.card (smaller.subgroupOf larger) := by
    simpa only [Nat.card_congr equivalence.toEquiv] using hcomplement
  have hcore := le_solvablePrimeComplementCore prime (smaller.subgroupOf larger)
    hnormal hrestrictedSolvable hrestrictedComplement
  have hmap := Subgroup.map_mono (f := larger.subtype) hcore
  simpa only [Subgroup.map_subgroupOf_eq_of_le hle, thetaCoreOf] using hmap

theorem thetaCoreOf_mono_of_normal {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (smaller larger : Subgroup G) (hle : smaller ≤ larger)
    (hnormal : (smaller.subgroupOf larger).Normal) : thetaCoreOf prime smaller ≤ thetaCoreOf prime larger := by
  apply normal_solvable_primeComplement_le_thetaCoreOf prime (thetaCoreOf prime smaller) larger
    ((thetaCoreOf_le prime smaller).trans hle)
  · rw [thetaCoreOf_subgroupOf prime hprime smaller larger hle]
    exact thetaCoreOf_normal_of_normal prime hprime (smaller.subgroupOf larger) hnormal
  · exact thetaCoreOf_solvable prime hprime smaller
  · exact thetaCoreOf_prime_complement prime hprime smaller

theorem normal_intersection_subgroupOf {G : Type u} [Group G]
    (subgroup normalSubgroup overgroup : Subgroup G) (hle : subgroup ≤ overgroup)
    (hnormalLe : normalSubgroup ≤ overgroup)
    (hnormal : (normalSubgroup.subgroupOf overgroup).Normal) :
    ((subgroup ⊓ normalSubgroup).subgroupOf subgroup).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (inf_le_left : subgroup ⊓ normalSubgroup ≤ subgroup)).mpr
  have hnormalizes := (Subgroup.normal_subgroupOf_iff_le_normalizer hnormalLe).mp hnormal
  intro element conjugator helement hconjugator
  exact ⟨subgroup.mul_mem (subgroup.mul_mem hconjugator helement.1)
    (subgroup.inv_mem hconjugator),
    Subgroup.le_normalizer_iff.mp hnormalizes conjugator (hle hconjugator) element helement.2⟩

theorem intersection_thetaCoreOf_le {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (smaller larger : Subgroup G) (hle : smaller ≤ larger) :
    smaller ⊓ thetaCoreOf prime larger ≤ thetaCoreOf prime smaller := by
  have hnormal : ((thetaCoreOf prime larger).subgroupOf larger).Normal := by
    have heq : (thetaCoreOf prime larger).subgroupOf larger = solvablePrimeComplementCore larger prime :=
      Subgroup.comap_map_eq_self_of_injective larger.subtype_injective _
    rw [heq]
    exact (solvablePrimeComplementCore_properties larger prime hprime).1
  have hintersectionNormal := normal_intersection_subgroupOf smaller (thetaCoreOf prime larger)
    larger hle (thetaCoreOf_le prime larger) hnormal
  have : Group.IsSolvable (thetaCoreOf prime larger) := thetaCoreOf_solvable prime hprime larger
  have hintersectionSolvable : Group.IsSolvable (smaller ⊓ thetaCoreOf prime larger : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective inf_le_right)
  have hcomplement : ¬prime ∣ Nat.card (smaller ⊓ thetaCoreOf prime larger : Subgroup G) :=
    fun hdiv => thetaCoreOf_prime_complement prime hprime larger
      (hdiv.trans (Subgroup.card_dvd_of_le inf_le_right))
  exact normal_solvable_primeComplement_le_thetaCoreOf prime _ smaller inf_le_left
    hintersectionNormal hintersectionSolvable hcomplement

theorem thetaCoreOf_normal_intersection {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (smaller larger : Subgroup G) (hle : smaller ≤ larger)
    (hnormal : (smaller.subgroupOf larger).Normal) :
    thetaCoreOf prime smaller = smaller ⊓ thetaCoreOf prime larger := by
  exact le_antisymm (le_inf (thetaCoreOf_le prime smaller)
    (thetaCoreOf_mono_of_normal prime hprime smaller larger hle hnormal))
    (intersection_thetaCoreOf_le prime hprime smaller larger hle)

theorem thetaCoreOf_subnormal_intersection {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) {smaller larger : Subgroup G}
    (hsubnormal : IsSubnormal smaller larger) :
    thetaCoreOf prime smaller = smaller ⊓ thetaCoreOf prime larger := by
  have hmono : thetaCoreOf prime smaller ≤ thetaCoreOf prime larger := by
    induction hsubnormal with
    | refl => exact le_rfl
    | step hle hnormal _ ih =>
      exact (thetaCoreOf_mono_of_normal prime hprime _ _ hle hnormal).trans ih
  exact le_antisymm (le_inf (thetaCoreOf_le prime smaller) hmono)
    (intersection_thetaCoreOf_le prime hprime smaller larger (subnormal_le hsubnormal))

end CFSG.RankThreeEvenClassification.Helpers
