module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Data.ZMod.QuotientGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p : ℕ} {A : Type*} [Group A]

def subgroupsOfCard (A : Type*) [Group A] (n : ℕ) : Set (Subgroup A) := {B | Nat.card B = n}

@[simp]
theorem mem_subgroupsOfCard {n : ℕ} {B : Subgroup A} :
    B ∈ subgroupsOfCard A n ↔ Nat.card B = n := Iff.rfl

theorem finite_subgroupsOfCard [Finite A] (n : ℕ) : (subgroupsOfCard A n).Finite :=
  Set.toFinite _

theorem orderOf_eq_of_pow_eq_one (hp : p.Prime) (hexp : ∀ a : A, a ^ p = 1) {a : A} (ha : a ≠ 1) :
    orderOf a = p := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hexp a)) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) ha
  · exact h

theorem zpowers_mem_subgroupsOfCard (hp : p.Prime) (hexp : ∀ a : A, a ^ p = 1) {a : A}
    (ha : a ≠ 1) : Subgroup.zpowers a ∈ subgroupsOfCard A p := by
  rw [mem_subgroupsOfCard, Nat.card_zpowers, orderOf_eq_of_pow_eq_one hp hexp ha]

theorem eq_zpowers_of_mem_subgroupsOfCard [Finite A] (hp : p.Prime) (hexp : ∀ a : A, a ^ p = 1)
    {B : Subgroup A} (hB : B ∈ subgroupsOfCard A p) {a : A} (ha : a ≠ 1) (haB : a ∈ B) :
    B = Subgroup.zpowers a := by
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haB) ?_).symm
  rw [Nat.card_zpowers, orderOf_eq_of_pow_eq_one hp hexp ha, mem_subgroupsOfCard.mp hB]

theorem existsUnique_mem_subgroupsOfCard [Finite A] (hp : p.Prime) (hexp : ∀ a : A, a ^ p = 1)
    {a : A} (ha : a ≠ 1) : ∃! B, B ∈ subgroupsOfCard A p ∧ a ∈ B := by
  refine ⟨Subgroup.zpowers a, ⟨zpowers_mem_subgroupsOfCard hp hexp ha, Subgroup.mem_zpowers a⟩, ?_⟩
  rintro C ⟨hC, haC⟩
  exact eq_zpowers_of_mem_subgroupsOfCard hp hexp hC ha haC

private theorem card_toFinset_eq_natCard {α : Type*} {s : Set α} (h : s.Finite) :
    h.toFinset.card = Nat.card s := by
  rw [← Set.ncard_eq_toFinset_card _ h, Nat.card_coe_set_eq]

theorem card_subgroupsOfCard_of_card_eq_sq (hp : p.Prime) (hcard : Nat.card A = p ^ 2)
    (hexp : ∀ a : A, a ^ p = 1) : Nat.card (subgroupsOfCard A p) = p + 1 := by
  classical
  have hA : Finite A := Nat.finite_of_card_ne_zero (by simp [hcard, hp.ne_zero])
  have := Fintype.ofFinite A
  have hLfin : (subgroupsOfCard A p).Finite := finite_subgroupsOfCard p
  set L := hLfin.toFinset with hLdef
  have hmaps : Set.MapsTo (fun a : A => Subgroup.zpowers a)
      ↑({a ∈ Finset.univ | a ≠ 1} : Finset A) ↑L := by
    intro a ha
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
    simpa [hLdef] using zpowers_mem_subgroupsOfCard hp hexp ha
  have hfib : ∀ B ∈ L,
      ({a ∈ ({a ∈ Finset.univ | a ≠ 1} : Finset A) | Subgroup.zpowers a = B}).card = p - 1 := by
    intro B hB
    have hB' : B ∈ subgroupsOfCard A p := by simpa [hLdef] using hB
    have heq : ({a ∈ ({a ∈ Finset.univ | a ≠ 1} : Finset A) | Subgroup.zpowers a = B})
        = (B : Set A).toFinset.erase 1 := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        Set.mem_toFinset, SetLike.mem_coe]
      exact ⟨fun ⟨ha1, hz⟩ => ⟨ha1, hz ▸ Subgroup.mem_zpowers a⟩, fun ⟨ha1, haB⟩ =>
        ⟨ha1, (eq_zpowers_of_mem_subgroupsOfCard hp hexp hB' ha1 haB).symm⟩⟩
    have hcardB : (B : Set A).toFinset.card = p := by
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
      exact mem_subgroupsOfCard.mp hB'
    rw [heq, Finset.card_erase_of_mem (by simp), hcardB]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hsum
  rw [Finset.filter_ne' Finset.univ 1, Finset.card_erase_of_mem (Finset.mem_univ 1),
    Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at hsum
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have hkey : (p + 1) * (p - 1) = Nat.card (subgroupsOfCard A p) * (p - 1) := by
    rw [← card_toFinset_eq_natCard hLfin, ← hLdef, ← hsum, ← Nat.sq_sub_sq]
  exact (Nat.eq_of_mul_eq_mul_right hp1 hkey).symm

theorem indicator_identity_of_card_eq_sq (hp : p.Prime) (hcard : Nat.card A = p ^ 2)
    (hexp : ∀ a : A, a ^ p = 1) (a : A) :
    p * ((⊥ : Subgroup A) : Set A).indicator (1 : A → ℕ) a
        + ((⊤ : Subgroup A) : Set A).indicator (1 : A → ℕ) a
      = ∑ᶠ B ∈ subgroupsOfCard A p, ((B : Set A).indicator (1 : A → ℕ) a) := by
  classical
  have hA : Finite A := Nat.finite_of_card_ne_zero (by simp [hcard, hp.ne_zero])
  have hLfin : (subgroupsOfCard A p).Finite := finite_subgroupsOfCard p
  rw [finsum_mem_eq_finite_toFinset_sum _ hLfin]
  have htop : ((⊤ : Subgroup A) : Set A).indicator (1 : A → ℕ) a = 1 := by simp
  by_cases ha : a = 1
  ·
    subst ha
    have hall : ∀ B ∈ hLfin.toFinset, ((B : Set A)).indicator (1 : A → ℕ) 1 = 1 := by
      intro B _; simp
    rw [Finset.sum_congr rfl hall, Finset.sum_const, htop,
      card_toFinset_eq_natCard hLfin, card_subgroupsOfCard_of_card_eq_sq hp hcard hexp]
    simp
  ·
    obtain ⟨B, ⟨hB, haB⟩, huniq⟩ := existsUnique_mem_subgroupsOfCard hp hexp ha
    have hbot : (((⊥ : Subgroup A) : Set A)).indicator (1 : A → ℕ) a = 0 := by simp [ha]
    rw [hbot, htop, mul_zero, zero_add,
      Finset.sum_eq_single_of_mem B (hLfin.mem_toFinset.mpr hB)]
    · simp [haB]
    · intro C hC hCB
      have hC' : C ∈ subgroupsOfCard A p := hLfin.mem_toFinset.mp hC
      simp only [Set.indicator_apply, SetLike.mem_coe, Pi.one_apply, ite_eq_right_iff]
      intro haC
      exact absurd (huniq C ⟨hC', haC⟩) hCB

section Iso

theorem card_eq_sq_of_mulEquiv (e : A ≃* Multiplicative (ZMod p × ZMod p)) (hp : p.Prime) :
    Nat.card A = p ^ 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card, sq]

theorem pow_eq_one_of_mulEquiv (e : A ≃* Multiplicative (ZMod p × ZMod p)) (hp : p.Prime)
    (a : A) : a ^ p = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine e.injective ?_
  rw [map_pow, map_one]
  have h : Multiplicative.toAdd (e a ^ p)
      = Multiplicative.toAdd (1 : Multiplicative (ZMod p × ZMod p)) := by
    simp [Prod.ext_iff]
  exact Multiplicative.toAdd.injective h

theorem card_subgroupsOfCard_of_mulEquiv (e : A ≃* Multiplicative (ZMod p × ZMod p))
    (hp : p.Prime) : Nat.card (subgroupsOfCard A p) = p + 1 :=
  card_subgroupsOfCard_of_card_eq_sq hp (card_eq_sq_of_mulEquiv e hp)
    (pow_eq_one_of_mulEquiv e hp)

theorem indicator_identity_of_mulEquiv (e : A ≃* Multiplicative (ZMod p × ZMod p))
    (hp : p.Prime) (a : A) :
    p * ((⊥ : Subgroup A) : Set A).indicator (1 : A → ℕ) a
        + ((⊤ : Subgroup A) : Set A).indicator (1 : A → ℕ) a
      = ∑ᶠ B ∈ subgroupsOfCard A p, ((B : Set A).indicator (1 : A → ℕ) a) :=
  indicator_identity_of_card_eq_sq hp (card_eq_sq_of_mulEquiv e hp)
    (pow_eq_one_of_mulEquiv e hp) a

end Iso

end CFSG.FeitThompson
