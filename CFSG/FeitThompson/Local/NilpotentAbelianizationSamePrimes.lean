module
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem natCard_abelianization_eq_index_commutator (G : Type*) [Group G] :
    Nat.card (Abelianization G) = (commutator G).index :=
  (Subgroup.index_eq_card _).symm

theorem surjective_abelianizationMap {G K : Type*} [Group G] [Group K] {f : G →* K}
    (hf : Function.Surjective f) : Function.Surjective (Abelianization.map f) := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutator K) x
  obtain ⟨g, rfl⟩ := hf a
  exact ⟨Abelianization.of g, Abelianization.map_of f g⟩

theorem index_commutator_dvd_of_surjective {G K : Type*} [Group G] [Group K] {f : G →* K}
    (hf : Function.Surjective f) : (commutator K).index ∣ (commutator G).index := by
  have h := Subgroup.card_dvd_of_surjective (surjective_abelianizationMap hf)
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact h

theorem prime_dvd_index_commutator_of_natCard_eq_prime_pow {q : ℕ} (hq : q.Prime) (Q : Type*)
    [Group Q] [Finite Q] [Nontrivial Q] [Group.IsSolvable Q] {a : ℕ} (hcard : Nat.card Q = q ^ a) :
    q ∣ (commutator Q).index := by
  have hdvd : (commutator Q).index ∣ q ^ a := hcard ▸ (commutator Q).index_dvd_card
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hq).1 hdvd
  have hne : (commutator Q).index ≠ 1 := fun h =>
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne (Subgroup.index_eq_one.1 h)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact absurd (by simpa using hk) hne
  · exact hk ▸ dvd_pow_self q hk0.ne'

variable (H : Type*) [Group H] [Finite H] [Group.IsNilpotent H]

theorem prime_dvd_index_commutator {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card H) :
    q ∣ (commutator H).index := by
  have hcardH : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hmem : q ∈ (Nat.card H).primeFactors := Nat.mem_primeFactors.2 ⟨hq, hdvd, hcardH⟩
  obtain ⟨P, -, hcard, ⟨e⟩⟩ := exists_mulEquiv_pi_normal_sylow H
  have hQcard : Nat.card (P ⟨q, hmem⟩) = q ^ (Nat.card H).factorization q := hcard ⟨q, hmem⟩
  have hpos : 0 < (Nat.card H).factorization q := hq.factorization_pos_of_dvd hcardH hdvd
  have : Nontrivial (P ⟨q, hmem⟩) := Finite.one_lt_card_iff_nontrivial.1 <| by
    rw [hQcard]; exact Nat.one_lt_pow hpos.ne' hq.one_lt
  have hsurj : Function.Surjective
      ((Pi.evalMonoidHom (fun p : (Nat.card H).primeFactors => (P p : Type _))
        ⟨q, hmem⟩).comp e.symm.toMonoidHom) :=
    (Function.surjective_eval _).comp e.symm.surjective
  exact (prime_dvd_index_commutator_of_natCard_eq_prime_pow hq _ hQcard).trans
    (index_commutator_dvd_of_surjective hsurj)

theorem prime_dvd_natCard_iff_dvd_index_commutator {q : ℕ} (hq : q.Prime) :
    q ∣ Nat.card H ↔ q ∣ (commutator H).index :=
  ⟨prime_dvd_index_commutator H hq, fun h => h.trans (commutator H).index_dvd_card⟩

theorem prime_dvd_natCard_iff_dvd_natCard_abelianization {q : ℕ} (hq : q.Prime) :
    q ∣ Nat.card H ↔ q ∣ Nat.card (Abelianization H) := by
  rw [natCard_abelianization_eq_index_commutator]
  exact prime_dvd_natCard_iff_dvd_index_commutator H hq

theorem primeFactors_natCard_eq_primeFactors_index_commutator :
    (Nat.card H).primeFactors = ((commutator H).index).primeFactors := by
  ext q
  simp only [Nat.mem_primeFactors, Nat.card_pos.ne', Subgroup.index_ne_zero_of_finite, ne_eq,
    not_false_eq_true, and_true]
  exact and_congr_right fun hq => prime_dvd_natCard_iff_dvd_index_commutator H hq

theorem exists_natCard_eq_prime_pow_of_index_commutator_eq_prime_pow {p a : ℕ} (hp : p.Prime)
    (h : (commutator H).index = p ^ a) : ∃ b, Nat.card H = p ^ b :=
  ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hd hdvd =>
    Nat.prime_eq_prime_of_dvd_pow hd hp (h ▸ prime_dvd_index_commutator H hd hdvd)⟩

theorem isPGroup_of_index_commutator_eq_prime_pow {p a : ℕ} (hp : p.Prime)
    (h : (commutator H).index = p ^ a) : IsPGroup p H := by
  obtain ⟨b, hb⟩ := exists_natCard_eq_prime_pow_of_index_commutator_eq_prime_pow H hp h
  exact IsPGroup.of_card hb

end CFSG.FeitThompson
