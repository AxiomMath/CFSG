module

public import CFSG.Assembly.OrderReductions.PrimeCoreQuotient
public import CFSG.Assembly.OrderReductions.SolvableComplementCentralizer

public section

namespace CFSG.OrderReductions.SolvableConjugatePairs

open CFSG.OrderReductions.PrimeCore CFSG.OrderReductions.PrimeComplementCore

@[expose] def conjugatePair {group : Type*} [Group group] (element conjugator : group) : Subgroup group :=
  Subgroup.closure ({element, conjugator⁻¹ * element * conjugator} : Set group)

theorem centralizes_coprime_normal_of_prime_pairs {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (normal : Subgroup group) [normal.Normal]
    (coprime : ¬ prime ∣ Nat.card normal) (element : group)
    (pairs : ∀ conjugator ∈ normal, IsPGroup prime (conjugatePair element conjugator)) :
    element ∈ Subgroup.centralizer (normal : Set group) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro conjugator membership
  let paired := conjugatePair element conjugator
  have element_mem : element ∈ paired := Subgroup.subset_closure (by simp)
  have conjugate_mem : conjugator⁻¹ * element * conjugator ∈ paired := Subgroup.subset_closure (by simp)
  have difference_mem : element⁻¹ * (conjugator⁻¹ * element * conjugator) ∈ paired :=
    paired.mul_mem (paired.inv_mem element_mem) conjugate_mem
  have difference_normal : element⁻¹ * (conjugator⁻¹ * element * conjugator) ∈ normal := by
    have conjugated := (inferInstance : normal.Normal).conj_mem conjugator⁻¹
      (normal.inv_mem membership) element⁻¹
    have multiplied := normal.mul_mem conjugated membership
    convert multiplied using 1
    group
  have disjoint := disjoint_of_primeComplement prime paired normal (pairs conjugator membership) coprime
  have difference_one : element⁻¹ * (conjugator⁻¹ * element * conjugator) = 1 :=
    Subgroup.mem_bot.mp (disjoint.le_bot ⟨difference_mem, difference_normal⟩)
  have conjugate_eq : conjugator⁻¹ * element * conjugator = element :=
    (inv_mul_eq_one.mp difference_one).symm
  have commutes := congrArg (fun member : group => conjugator * member) conjugate_eq
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using commutes.symm

theorem prime_element_trivial_of_pairs_and_trivial_core {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (core_bot : primeCore prime group = ⊥) (element : group)
    (prime_element : IsPGroup prime (Subgroup.zpowers element))
    (pairs : ∀ conjugator : group, IsPGroup prime (conjugatePair element conjugator)) : element = 1 := by
  have centralizes := centralizes_coprime_normal_of_prime_pairs prime (primeComplementCore prime group)
    (primeComplementCore_coprime prime group) element (fun conjugator _ => pairs conjugator)
  have mem_core := CFSG.OrderReductions.SolvableComplementCentralizer.centralizer_complementCore_le prime core_bot centralizes
  have disjoint := disjoint_of_primeComplement prime (Subgroup.zpowers element) (primeComplementCore prime group)
    prime_element (primeComplementCore_coprime prime group)
  exact Subgroup.mem_bot.mp (disjoint.le_bot ⟨Subgroup.mem_zpowers element, mem_core⟩)

theorem mem_primeCore_of_conjugate_pairs {group : Type*} [Group group] [Finite group]
    [Group.IsSolvable group] (prime : ℕ) [Fact (Nat.Prime prime)] (element : group)
    (prime_element : IsPGroup prime (Subgroup.zpowers element))
    (pairs : ∀ conjugator : group, IsPGroup prime (conjugatePair element conjugator)) :
    element ∈ primeCore prime group := by
  let core := primeCore prime group
  let projection := QuotientGroup.mk' core
  have image_prime : IsPGroup prime (Subgroup.zpowers (projection element)) := by
    rw [← MonoidHom.map_zpowers]
    exact prime_element.map projection
  have image_pairs : ∀ conjugator : group ⧸ core, IsPGroup prime (conjugatePair (projection element) conjugator) := by
    intro conjugator
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective core conjugator
    have image_eq : (conjugatePair element original).map projection =
        conjugatePair (projection element) (projection original) := by
      rw [conjugatePair, MonoidHom.map_closure]
      simp only [Set.image_insert_eq, Set.image_singleton, map_mul, map_inv]
      rfl
    rw [← image_eq]
    exact (pairs original).map projection
  have image_one := prime_element_trivial_of_pairs_and_trivial_core prime
    (CFSG.OrderReductions.PrimeCoreQuotient.primeCore_quotient_eq_bot prime) (projection element) image_prime image_pairs
  exact (QuotientGroup.eq_one_iff _).mp image_one

end CFSG.OrderReductions.SolvableConjugatePairs
