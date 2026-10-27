module

public import CFSG.FeitThompson.Definitions.DadeData
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

theorem isPiNumber_empty_iff {n : ℕ} (hn : n ≠ 0) : IsPiNumber (∅ : Set ℕ) n ↔ n = 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ isPiNumber_one⟩
  have hpf : n.primeFactors = ∅ := by
    ext p; simpa using fun hp => isPiNumber_iff.1 h p hp
  exact (Nat.primeFactors_eq_empty.1 hpf).resolve_left hn

theorem coprime_of_isPiNumber_compl {π : Set ℕ} {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmπ : IsPiNumber πᶜ m) (hnπ : IsPiNumber π n) : Nat.Coprime m n :=
  (hnπ.coprime_of_compl hmπ hn hm).symm

theorem le_of_coprime_natCard_index {X : Type*} [Group X] {N K : Subgroup X} [N.Normal]
    (h : Nat.Coprime (Nat.card K) N.index) : K ≤ N := by
  rw [← Subgroup.relIndex_eq_one]
  exact Nat.eq_one_of_dvd_one
    (h ▸ Nat.dvd_gcd (Subgroup.index_dvd_card _) (Subgroup.relIndex_dvd_index_of_normal N K))

theorem le_of_isPiNumber_compl {X : Type*} [Group X] [Finite X] {π : Set ℕ} {N K : Subgroup X}
    [N.Normal] (hNidx : IsPiNumber π N.index) (hK : IsPiNumber πᶜ (Nat.card K)) : K ≤ N :=
  le_of_coprime_natCard_index
    (coprime_of_isPiNumber_compl Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite hK hNidx)

def dadePrimes (L : Subgroup G) (A : Set G) : Set ℕ :=
  {p | ∃ b ∈ A, p ∈ (Nat.card ↥(L ⊓ Subgroup.centralizer ({b} : Set G))).primeFactors}

theorem mem_dadePrimes_iff {L : Subgroup G} {A : Set G} {p : ℕ} :
    p ∈ dadePrimes L A ↔
      ∃ b ∈ A, p ∈ (Nat.card ↥(L ⊓ Subgroup.centralizer ({b} : Set G))).primeFactors := Iff.rfl

theorem prime_of_mem_dadePrimes {L : Subgroup G} {A : Set G} {p : ℕ} (hp : p ∈ dadePrimes L A) :
    p.Prime := Nat.prime_of_mem_primeFactors hp.choose_spec.2

@[simp] theorem dadePrimes_empty (L : Subgroup G) : dadePrimes L (∅ : Set G) = ∅ := by
  ext p; simp [dadePrimes]

theorem dadePrimes_mono {L : Subgroup G} {A B : Set G} (h : A ⊆ B) :
    dadePrimes L A ⊆ dadePrimes L B := fun _ ⟨b, hb, hp⟩ => ⟨b, h hb, hp⟩

namespace IsDadeData

variable [Finite G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G} {a : G}

omit [Finite G] in
theorem isPiNumber_card_inf_centralizer (ha : a ∈ A) :
    IsPiNumber (dadePrimes L A) (Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set G))) :=
  isPiNumber_iff.2 fun _ hp => ⟨a, ha, hp⟩

omit [Finite G] in
theorem isPiSubgroup_inf_centralizer (ha : a ∈ A) :
    IsPiSubgroup (dadePrimes L A) (L ⊓ Subgroup.centralizer ({a} : Set G)) :=
  isPiSubgroup_iff_isPiNumber.2 (isPiNumber_card_inf_centralizer ha)

theorem isPiNumber_compl_card_H (hD : IsDadeData L A H) (ha : a ∈ A) :
    IsPiNumber (dadePrimes L A)ᶜ (Nat.card ↥(H a)) := by
  rw [isPiNumber_compl_iff]
  intro p hp hmem
  obtain ⟨b, hb, hpb⟩ := mem_dadePrimes_iff.1 hmem
  exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne'
    (Nat.dvd_one.1 (hD.coprime_card ha hb ▸
      Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hpb)))

theorem card_subgroupOf_H (hD : IsDadeData L A H) (ha : a ∈ A) :
    Nat.card ↥((H a).subgroupOf (Subgroup.centralizer ({a} : Set G))) = Nat.card ↥(H a) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hD.le_centralizer ha)).toEquiv

theorem index_subgroupOf_H (hD : IsDadeData L A H) (ha : a ∈ A) :
    ((H a).subgroupOf (Subgroup.centralizer ({a} : Set G))).index =
      Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have h1 := Subgroup.index_mul_card ((H a).subgroupOf (Subgroup.centralizer ({a} : Set G)))
  rw [hD.card_subgroupOf_H ha] at h1
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H a)) ?_
  rw [h1, ← hD.card_mul_card ha, Nat.mul_comm]

theorem isPiNumber_index_subgroupOf_H (hD : IsDadeData L A H) (ha : a ∈ A) :
    IsPiNumber (dadePrimes L A)
      (((H a).subgroupOf (Subgroup.centralizer ({a} : Set G))).index) := by
  rw [hD.index_subgroupOf_H ha]; exact isPiNumber_card_inf_centralizer ha

theorem coprime_card_index_H (hD : IsDadeData L A H) (ha : a ∈ A) :
    Nat.Coprime (Nat.card ↥(H a))
      (((H a).subgroupOf (Subgroup.centralizer ({a} : Set G))).index) :=
  coprime_of_isPiNumber_compl Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite
    (hD.isPiNumber_compl_card_H ha) (hD.isPiNumber_index_subgroupOf_H ha)

theorem le_H_of_isPiNumber_compl (hD : IsDadeData L A H) (ha : a ∈ A) {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : IsPiNumber (dadePrimes L A)ᶜ (Nat.card ↥K)) : K ≤ H a := by
  have := hD.normal_subgroupOf ha
  have h : K.subgroupOf (Subgroup.centralizer ({a} : Set G)) ≤
      (H a).subgroupOf (Subgroup.centralizer ({a} : Set G)) := by
    refine le_of_isPiNumber_compl (hD.isPiNumber_index_subgroupOf_H ha) ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv]
  intro x hx
  exact h (show (⟨x, hKC hx⟩ : Subgroup.centralizer ({a} : Set G)) ∈ _ from hx)

theorem eq_H_of_normal (hD : IsDadeData L A H) (ha : a ∈ A) {N : Subgroup G}
    (hNC : N ≤ Subgroup.centralizer ({a} : Set G))
    (hN : (N.subgroupOf (Subgroup.centralizer ({a} : Set G))).Normal)
    (hNcard : IsPiNumber (dadePrimes L A)ᶜ (Nat.card ↥N))
    (hNidx : IsPiNumber (dadePrimes L A)
      ((N.subgroupOf (Subgroup.centralizer ({a} : Set G))).index)) :
    N = H a := by
  have := hN
  refine le_antisymm (hD.le_H_of_isPiNumber_compl ha hNC hNcard) fun x hx => ?_
  have h : (H a).subgroupOf (Subgroup.centralizer ({a} : Set G)) ≤
      N.subgroupOf (Subgroup.centralizer ({a} : Set G)) := by
    refine le_of_isPiNumber_compl hNidx ?_
    rw [hD.card_subgroupOf_H ha]
    exact hD.isPiNumber_compl_card_H ha
  exact h (show (⟨x, hD.le_centralizer ha hx⟩ : Subgroup.centralizer ({a} : Set G)) ∈ _ from hx)

end IsDadeData

end

end CFSG.FeitThompson
