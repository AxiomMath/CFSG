module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallFoundations

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem PrimeSetOrder.map {G : Type u} {H : Type v} [Group G] [Group H]
    (primes : Set ℕ) (subgroup : Subgroup G) (homomorphism : G →* H)
    (horder : PrimeSetOrder primes (Nat.card subgroup)) :
    PrimeSetOrder primes (Nat.card (subgroup.map homomorphism)) :=
  PrimeSetOrder.of_dvd primes _ _ horder (Subgroup.card_map_dvd subgroup homomorphism)

theorem PrimeSetOrder.subgroupOf {G : Type u} [Group G]
    (primes : Set ℕ) (subgroup overgroup : Subgroup G) (hle : subgroup ≤ overgroup)
    (horder : PrimeSetOrder primes (Nat.card subgroup)) :
    PrimeSetOrder primes (Nat.card (subgroup.subgroupOf overgroup)) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact horder

theorem PrimeSetOrder.subgroupOf_any {G : Type u} [Group G]
    (primes : Set ℕ) (subgroup overgroup : Subgroup G)
    (horder : PrimeSetOrder primes (Nat.card subgroup)) :
    PrimeSetOrder primes (Nat.card (subgroup.subgroupOf overgroup)) := by
  rw [← Subgroup.inf_subgroupOf_right subgroup overgroup]
  exact PrimeSetOrder.subgroupOf primes (subgroup ⊓ overgroup) overgroup inf_le_right
    (PrimeSetOrder.of_dvd primes _ _ horder (Subgroup.card_dvd_of_le inf_le_left))

theorem HallFor.map {G : Type u} {H : Type v} [Group G] [Group H]
    (primes : Set ℕ) (subgroup : Subgroup G) (homomorphism : G →* H)
    (hsurjective : Function.Surjective homomorphism) (hhall : HallFor primes subgroup) :
    HallFor primes (subgroup.map homomorphism) :=
  ⟨PrimeSetOrder.map primes subgroup homomorphism hhall.1,
    PrimeSetOrder.of_dvd primesᶜ _ _ hhall.2 (subgroup.index_map_dvd hsurjective)⟩

theorem HallFor.subgroupOf {G : Type u} [Group G]
    (primes : Set ℕ) (subgroup overgroup : Subgroup G) (hle : subgroup ≤ overgroup)
    (hhall : HallFor primes subgroup) : HallFor primes (subgroup.subgroupOf overgroup) := by
  refine ⟨PrimeSetOrder.subgroupOf primes subgroup overgroup hle hhall.1, ?_⟩
  have hindex : (subgroup.subgroupOf overgroup).index ∣ subgroup.index := by
    have heq := Subgroup.index_map_subtype (subgroup.subgroupOf overgroup)
    rw [Subgroup.map_subgroupOf_eq_of_le hle] at heq
    rw [heq]
    exact dvd_mul_right _ _
  exact PrimeSetOrder.of_dvd primesᶜ _ _ hhall.2 hindex

theorem HallFor.eq_top_of_primeSetOrder {G : Type u} [Group G] [Finite G]
    (primes : Set ℕ) (subgroup : Subgroup G) (hhall : HallFor primes subgroup)
    (horder : PrimeSetOrder primes (Nat.card G)) : subgroup = ⊤ := by
  apply Subgroup.index_eq_one.mp
  exact Nat.eq_one_of_dvd_coprimes
    (PrimeSetOrder.coprime_compl primes _ _ horder hhall.2)
    subgroup.index_dvd_card dvd_rfl

theorem HallFor.eq_of_le {G : Type u} [Group G] [Finite G]
    (primes : Set ℕ) (first second : Subgroup G)
    (hfirst : HallFor primes first) (hsecond : HallFor primes second) (hle : first ≤ second) :
    first = second := by
  have heq := HallFor.eq_top_of_primeSetOrder primes (first.subgroupOf second)
    (HallFor.subgroupOf primes first second hle hfirst) hsecond.1
  calc
    first = (first.subgroupOf second).map second.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hle).symm
    _ = second := by rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem normalized_sup_primeSetOrder {G : Type u} [Group G]
    (primes : Set ℕ) (first second : Subgroup G)
    (hnormalizes : second ≤ Subgroup.normalizer (first : Set G))
    (hfirst : PrimeSetOrder primes (Nat.card first))
    (hsecond : PrimeSetOrder primes (Nat.card second)) :
    PrimeSetOrder primes (Nat.card (first ⊔ second : Subgroup G)) := by
  have : (first.subgroupOf (second ⊔ first)).Normal :=
    normal_subgroupOf_of_normalizes first (second ⊔ first)
      (sup_le hnormalizes Subgroup.le_normalizer)
  have : (first.subgroupOf second).Normal :=
    normal_subgroupOf_of_normalizes first second hnormalizes
  let equivalence := QuotientGroup.quotientInfEquivProdNormalizerQuotient second first hnormalizes
  have hquotientCard : Nat.card ((second ⊔ first : Subgroup G) ⧸
      first.subgroupOf (second ⊔ first)) ∣ Nat.card second := by
    rw [← Nat.card_congr equivalence.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  have hrestrictedCard : Nat.card (first.subgroupOf (second ⊔ first)) = Nat.card first :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show first ≤ second ⊔ first from le_sup_right)).toEquiv
  rw [sup_comm first second,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (first.subgroupOf (second ⊔ first)),
    hrestrictedCard]
  exact PrimeSetOrder.mul primes _ _
    (PrimeSetOrder.of_dvd primes _ _ hsecond hquotientCard) hfirst

theorem normal_primeSetOrder_le_hall {G : Type u} [Group G] [Finite G]
    (primes : Set ℕ) (normalSubgroup hall : Subgroup G) [normalSubgroup.Normal]
    (horder : PrimeSetOrder primes (Nat.card normalSubgroup)) (hhall : HallFor primes hall) :
    normalSubgroup ≤ hall := by
  have hsupOrder := normalized_sup_primeSetOrder primes normalSubgroup hall
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) horder hhall.1
  have heq := HallFor.eq_top_of_primeSetOrder primes (hall.subgroupOf (normalSubgroup ⊔ hall))
    (HallFor.subgroupOf primes hall (normalSubgroup ⊔ hall) le_sup_right hhall) hsupOrder
  have hsupLe : normalSubgroup ⊔ hall ≤ hall := by
    intro element helement
    have hmem : (⟨element, helement⟩ : (normalSubgroup ⊔ hall : Subgroup G)) ∈
        hall.subgroupOf (normalSubgroup ⊔ hall) := by rw [heq]; exact Subgroup.mem_top _
    exact hmem
  exact le_sup_left.trans hsupLe

theorem normal_complement_of_sup_eq_top_and_coprime {G : Type u} [Group G]
    (normalSubgroup complement : Subgroup G) [normalSubgroup.Normal]
    (hsup : normalSubgroup ⊔ complement = ⊤)
    (hcoprime : (Nat.card normalSubgroup).Coprime (Nat.card complement)) :
    normalSubgroup.IsComplement' complement := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    (Subgroup.disjoint_of_coprime_natCard hcoprime)
  apply Set.eq_univ_of_forall
  intro element
  have hmem : element ∈ normalSubgroup ⊔ complement := by rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨first, hfirst, second, hsecond, heq⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  exact Set.mem_mul.mpr ⟨first, hfirst, second, hsecond, heq⟩

theorem normal_complement_subgroupOf {G : Type u} [Group G]
    (normalSubgroup complement overgroup : Subgroup G) [normalSubgroup.Normal]
    (hcomplement : normalSubgroup.IsComplement' complement) (hle : normalSubgroup ≤ overgroup) :
    (normalSubgroup.subgroupOf overgroup).IsComplement' (complement.subgroupOf overgroup) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.mpr
    intro element hnormal hcomplementMem
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hcomplement.disjoint hnormal hcomplementMem
  · apply Set.eq_univ_of_forall
    intro element
    have hmem : (element : G) ∈ normalSubgroup ⊔ complement := by
      rw [hcomplement.sup_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨first, hfirst, second, hsecond, heq⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hsecondOvergroup : second ∈ overgroup := by
      have hproduct := overgroup.mul_mem (overgroup.inv_mem (hle hfirst)) element.property
      rw [← heq, inv_mul_cancel_left] at hproduct
      exact hproduct
    exact Set.mem_mul.mpr ⟨⟨first, hle hfirst⟩, hfirst, ⟨second, hsecondOvergroup⟩,
      hsecond, Subtype.ext heq⟩

end CFSG.RankThreeEvenClassification.Helpers
