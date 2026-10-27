module

public import CFSG.GH74.KGroups.Generic
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.CharacterTheory.Burnside
public import Mathlib.Tactic.Basify

public section

namespace CFSG.GH74.KGroups

open CFSG.Certificates CFSG.Sporadic.Schreier

variable {n : ℕ}

@[expose] def elemsT (Q : RawSchreierDatum n) : List (Equiv.Perm (Fin n)) :=
  (enumeration Q).map tab

theorem elemsT_eq (Q : RawSchreierDatum n) : elemsT Q = enumeration Q := by
  have h : (tab : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) = id := funext tab_eq
  rw [elemsT, h, List.map_id]

theorem mem_elemsT (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (g : Equiv.Perm (Fin n)) :
    g ∈ elemsT Q ↔ g ∈ Q.originalSubgroup := by
  rw [elemsT_eq]
  exact mem_enumeration_iff Q hQ g

theorem nodup_elemsT (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) : (elemsT Q).Nodup := by
  rw [elemsT_eq]
  exact enumeration_nodup Q hQ

theorem forall_of_all (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {p : Equiv.Perm (Fin n) → Bool} (h : (elemsT Q).all p = true) :
    ∀ g ∈ Q.originalSubgroup, p g = true :=
  fun g hg => List.all_eq_true.1 h g ((mem_elemsT Q hQ g).2 hg)

theorem mem_iff_sift (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (g : Equiv.Perm (Fin n)) :
    g ∈ Q.originalSubgroup ↔ Q.sift g 0 = true :=
  (RawSchreierDatum.sift_eq_true_iff_mem_original Q hQ g).symm

theorem card_group (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) :
    Nat.card Q.originalSubgroup = Q.orderCertificate :=
  (Q.orderCertificate_eq_card hQ).symm

theorem card_filter (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (p : Equiv.Perm (Fin n) → Prop) [DecidablePred p] :
    Nat.card {g : Q.originalSubgroup // p g} =
      ((elemsT Q).filter (fun g => decide (p g))).length := by
  refine card_eq_length (fun g : Q.originalSubgroup => p g) (fun g => (g : Equiv.Perm (Fin n)))
    Subtype.val_injective _ ((nodup_elemsT Q hQ).filter _) ?_
  intro b
  simp only [List.mem_filter, decide_eq_true_eq, mem_elemsT Q hQ]
  constructor
  · rintro ⟨hb, hp⟩
    exact ⟨⟨b, hb⟩, hp, rfl⟩
  · rintro ⟨a, hp, rfl⟩
    exact ⟨a.2, hp⟩

@[expose] def pairInvB {M : Type*} [Monoid M] [DecidableEq M] (ws : List (List Bool × ℕ))
    (a b : M) : Bool :=
  ws.all fun wk => orderIs (evalW a b wk.1) wk.2

theorem pairInvB_iff {M : Type*} [Monoid M] [DecidableEq M] (ws : List (List Bool × ℕ))
    (hws : ∀ wk ∈ ws, 0 < wk.2) (a b : M) : pairInvB ws a b = true ↔ PairInv ws a b := by
  simp only [pairInvB, PairInv, List.all_eq_true]
  constructor
  · intro h wk hwk
    exact (orderIs_iff _ (hws wk hwk)).1 (h wk hwk)
  · intro h wk hwk
    exact (orderIs_iff _ (hws wk hwk)).2 (h wk hwk)

theorem card_pairs (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (oa ob : ℕ) (hoa : 0 < oa)
    (hob : 0 < ob) (ws : List (List Bool × ℕ)) (hws : ∀ wk ∈ ws, 0 < wk.2) :
    Nat.card {p : Q.originalSubgroup × Q.originalSubgroup //
        orderOf p.1 = oa ∧ orderOf p.2 = ob ∧ PairInv ws p.1 p.2} =
      ((((elemsT Q).filter (fun g => orderIs g oa)) ×ˢ
          ((elemsT Q).filter (fun g => orderIs g ob))).filter
        (fun q => pairInvB ws q.1 q.2)).length := by
  have hcoe : ∀ (x y : Q.originalSubgroup),
      PairInv ws x y ↔ PairInv ws (x : Equiv.Perm (Fin n)) (y : Equiv.Perm (Fin n)) := by
    intro x y
    simp only [PairInv]
    refine forall_congr' fun wk => forall_congr' fun _ => ?_
    have h := map_evalW (Q.originalSubgroup.subtype) x y wk.1
    have h' : ((evalW x y wk.1 : Q.originalSubgroup) : Equiv.Perm (Fin n)) =
        evalW (x : Equiv.Perm (Fin n)) (y : Equiv.Perm (Fin n)) wk.1 := h
    rw [← h', Subgroup.orderOf_coe]
  refine card_eq_length (fun p : Q.originalSubgroup × Q.originalSubgroup =>
      orderOf p.1 = oa ∧ orderOf p.2 = ob ∧ PairInv ws p.1 p.2)
    (fun p => ((p.1 : Equiv.Perm (Fin n)), (p.2 : Equiv.Perm (Fin n)))) ?_ _
    ((((nodup_elemsT Q hQ).filter _).product ((nodup_elemsT Q hQ).filter _)).filter _) ?_
  · intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  · rintro ⟨x, y⟩
    simp only [List.mem_filter, List.mem_product, mem_elemsT Q hQ]
    constructor
    · rintro ⟨⟨⟨hx, hxo⟩, hy, hyo⟩, hinv⟩
      refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ⟨?_, ?_, ?_⟩, rfl⟩
      · rw [← Subgroup.orderOf_coe]; exact (orderIs_iff _ hoa).1 hxo
      · rw [← Subgroup.orderOf_coe]; exact (orderIs_iff _ hob).1 hyo
      · exact (hcoe _ _).2 ((pairInvB_iff ws hws x y).1 hinv)
    · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, h⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨⟨⟨a.2, (orderIs_iff _ hoa).2 ?_⟩, b.2, (orderIs_iff _ hob).2 ?_⟩,
        (pairInvB_iff ws hws _ _).2 ((hcoe _ _).1 hab)⟩
      · rw [← Subgroup.orderOf_coe] at ha; exact ha
      · rw [← Subgroup.orderOf_coe] at hb; exact hb


theorem exists_pq_of_primeFactors_card_le_two (n : ℕ) (hn : n ≠ 0)
    (h : n.primeFactors.card ≤ 2) :
    ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p ^ a * q ^ b := by
  have hprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rfl
  have hcases : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · rw [Finset.card_eq_zero] at h0
    refine ⟨2, 3, 0, 0, Nat.prime_two, Nat.prime_three, by norm_num, ?_⟩
    conv_lhs => rw [hprod, h0]
    simp
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h1
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; simp)
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨2, 3, n.factorization 2, 0, Nat.prime_two, Nat.prime_three, by norm_num, ?_⟩
      conv_lhs => rw [hprod, hp]
      simp
    · refine ⟨p, 2, n.factorization p, 0, hpp, Nat.prime_two, hp2, ?_⟩
      conv_lhs => rw [hprod, hp]
      simp
  · obtain ⟨p, q, hpq, hpqe⟩ := Finset.card_eq_two.1 h2
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hpqe]; simp)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hpqe]; simp)
    refine ⟨p, q, n.factorization p, n.factorization q, hpp, hqp, hpq, ?_⟩
    conv_lhs => rw [hprod, hpqe, Finset.prod_pair hpq]

theorem isSolvable_of_two_primes {H : Type*} [Group H] [Finite H]
    (h : (Nat.card H).primeFactors.card ≤ 2) : Group.IsSolvable H := by
  obtain ⟨p, q, a, b, hp, hq, hpq, hcard⟩ :=
    exists_pq_of_primeFactors_card_le_two (Nat.card H) Nat.card_pos.ne' h
  have := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)

theorem card_inf_centralizer (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (τ : Equiv.Perm (Fin n)) :
    Nat.card ↥(Q.originalSubgroup ⊓ Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin n)))) =
      ((elemsT Q).filter (fun g => decide (g * τ = τ * g))).length := by
  refine card_eq_length (fun g : Equiv.Perm (Fin n) =>
      g ∈ Q.originalSubgroup ⊓ Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin n))))
    id Function.injective_id _ ((nodup_elemsT Q hQ).filter _) ?_
  intro b
  simp only [List.mem_filter, decide_eq_true_eq, mem_elemsT Q hQ, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, id_eq, exists_eq_right]

end CFSG.GH74.KGroups
