module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Local.PCoreSelfCentralizingNoNormalComplement
import CFSG.FeitThompson.Local.OddRankTwoAutomorphismDerivedPrimePower
import CFSG.FeitThompson.Local.NondefiningOddPrimesBelowDefining
import CFSG.FeitThompson.Local.ExponentPrimeRankTwoOrderCube
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.FiniteHomImageOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p q : ℕ} {X : Type*} [Group X] [Finite X]

private theorem isPGroup_ker_conjNormal_pCore (hp : p.Prime) [Group.IsSolvable X]
    (hcore : pComplCore p X = ⊥) :
    IsPGroup p (MulAut.conjNormal (G := X) (H := pCore p X)).ker :=
  have := pCore_normal p X
  (isPGroup_pCore hp X).to_le
    ((ker_conjNormal (pCore p X)) ▸ centralizer_pCore_le_pCore hp hcore)

private theorem elementaryAbelianPRank_pCore_le_two (hp : p.Prime)
    (hrank : elementaryAbelianPRank p X ≤ 2) : elementaryAbelianPRank p (pCore p X) ≤ 2 :=
  (elementaryAbelianPRank_subgroup_le hp.one_lt _).trans hrank

theorem isPGroup_commutator_of_pComplCore_eq_bot [Group.IsSolvable X] (hp : p.Prime)
    (hpodd : Odd p) (hodd : Odd (Nat.card X)) (hcore : pComplCore p X = ⊥)
    (hrank : elementaryAbelianPRank p X ≤ 2) : IsPGroup p (_root_.commutator X) :=
  have := pCore_normal p X
  isPGroup_commutator_of_hom _ (isPGroup_ker_conjNormal_pCore hp hcore)
    (isPGroup_commutator_subgroup_of_odd_aut_of_elementaryAbelianPRank_le_two hp hpodd
      (isPGroup_pCore hp X) (elementaryAbelianPRank_pCore_le_two hp hrank)
      (hodd.of_dvd_nat (Subgroup.card_range_dvd _)))

theorem commutator_le_pCore_of_pComplCore_eq_bot [Group.IsSolvable X] (hp : p.Prime)
    (hpodd : Odd p) (hodd : Odd (Nat.card X)) (hcore : pComplCore p X = ⊥)
    (hrank : elementaryAbelianPRank p X ≤ 2) : _root_.commutator X ≤ pCore p X :=
  le_pCore hp inferInstance
    (isPGroup_commutator_of_pComplCore_eq_bot hp hpodd hodd hcore hrank)

theorem closure_setOf_inv_mul_inv_mul_mul_le_pCore_of_pComplCore_eq_bot [Group.IsSolvable X]
    (hp : p.Prime) (hpodd : Odd p) (hodd : Odd (Nat.card X)) (hcore : pComplCore p X = ⊥)
    (hrank : elementaryAbelianPRank p X ≤ 2) :
    Subgroup.closure
        {g : X | ∃ a ∈ (⊤ : Subgroup X), ∃ b ∈ (⊤ : Subgroup X), a⁻¹ * b⁻¹ * a * b = g} ≤
      pCore p X := by
  rw [closure_setOf_inv_mul_inv_mul_mul, ← commutator_def]
  exact commutator_le_pCore_of_pComplCore_eq_bot hp hpodd hodd hcore hrank

theorem isMulCommutative_quotient_pCore_of_pComplCore_eq_bot [Group.IsSolvable X] (hp : p.Prime)
    (hpodd : Odd p) (hodd : Odd (Nat.card X)) (hcore : pComplCore p X = ⊥)
    (hrank : elementaryAbelianPRank p X ≤ 2) : IsMulCommutative (X ⧸ pCore p X) :=
  have := pCore_normal p X
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2
    (commutator_le_pCore_of_pComplCore_eq_bot hp hpodd hodd hcore hrank)

theorem not_dvd_card_quotient_pCore_of_pComplCore_eq_bot [Group.IsSolvable X] (hp : p.Prime)
    (hpodd : Odd p) (hodd : Odd (Nat.card X)) (hcore : pComplCore p X = ⊥)
    (hrank : elementaryAbelianPRank p X ≤ 2) : ¬ p ∣ Nat.card (X ⧸ pCore p X) := by
  have := Fact.mk hp
  have := pCore_normal p X
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set Q : Subgroup (X ⧸ pCore p X) := zpowers x with hQ
  have hQp : IsPGroup p (Q.comap (QuotientGroup.mk' (pCore p X))) :=
    (IsPGroup.iff_card.2 ⟨1, by rw [hQ, Nat.card_zpowers, hx, pow_one]⟩).comap_of_ker_isPGroup _
      (by rw [QuotientGroup.ker_mk']; exact isPGroup_pCore hp X)
  have := isMulCommutative_quotient_pCore_of_pComplCore_eq_bot hp hpodd hodd hcore hrank
  have hQn : (Q.comap (QuotientGroup.mk' (pCore p X))).Normal :=
    (Subgroup.normal_of_isMulCommutative Q).comap _
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (s := pCore p X) x
  have hx1 : x = 1 :=
    hy ▸ (QuotientGroup.eq_one_iff y).2 (le_pCore hp hQn hQp (by simp [hy, hQ, mem_zpowers]))
  rw [hx1, orderOf_one] at hx
  exact hp.one_lt.ne hx

theorem coprime_card_quotient_pCore_of_pComplCore_eq_bot [Group.IsSolvable X] (hp : p.Prime)
    (hpodd : Odd p) (hodd : Odd (Nat.card X)) (hcore : pComplCore p X = ⊥)
    (hrank : elementaryAbelianPRank p X ≤ 2) : Nat.Coprime (Nat.card (X ⧸ pCore p X)) p :=
  ((hp.coprime_iff_not_dvd).2
    (not_dvd_card_quotient_pCore_of_pComplCore_eq_bot hp hpodd hodd hcore hrank)).symm

theorem not_dvd_index_pCore_of_pComplCore_eq_bot [Group.IsSolvable X] (hp : p.Prime)
    (hpodd : Odd p) (hodd : Odd (Nat.card X)) (hcore : pComplCore p X = ⊥)
    (hrank : elementaryAbelianPRank p X ≤ 2) : ¬ p ∣ (pCore p X).index := by
  rw [Subgroup.index_eq_card]
  exact not_dvd_card_quotient_pCore_of_pComplCore_eq_bot hp hpodd hodd hcore hrank

theorem exists_sylow_coe_eq_pCore_of_pComplCore_eq_bot [Group.IsSolvable X] (hp : p.Prime)
    (hpodd : Odd p) (hodd : Odd (Nat.card X)) (hcore : pComplCore p X = ⊥)
    (hrank : elementaryAbelianPRank p X ≤ 2) : ∃ S : Sylow p X, (S : Subgroup X) = pCore p X :=
  have := Fact.mk hp
  ⟨(isPGroup_pCore hp X).toSylow
    (not_dvd_index_pCore_of_pComplCore_eq_bot hp hpodd hodd hcore hrank),
    IsPGroup.toSylow_coe _ _⟩

theorem prime_le_of_dvd_card_of_pComplCore_eq_bot [Group.IsSolvable X] (hp : p.Prime)
    (hpodd : Odd p) (hodd : Odd (Nat.card X)) (hcore : pComplCore p X = ⊥)
    (hrank : elementaryAbelianPRank p X ≤ 2) (hq : q.Prime) (hqX : q ∣ Nat.card X) : q ≤ p := by
  rcases eq_or_ne q p with rfl | hqp
  · exact le_rfl
  have := pCore_normal p X
  have := Fact.mk hp
  set g := MulAut.conjNormal (G := X) (H := pCore p X) with hg
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_ker_conjNormal_pCore hp hcore)
  have hqA : q ∣ Nat.card g.range := by
    rw [← natCard_range_mul_natCard_ker g, hk] at hqX
    rcases (Nat.Prime.dvd_mul hq).1 hqX with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)) hqp
  exact (prime_lt_of_dvd_card_of_odd_of_elementaryAbelianPRank_le_two hp hpodd
    (isPGroup_pCore hp X) (elementaryAbelianPRank_pCore_le_two hp hrank)
    (hodd.of_dvd_nat (Subgroup.card_range_dvd g)) hq hqp hqA).le

theorem rank_two_trivial_pComplCore_core [Group.IsSolvable X] (hp : p.Prime) (hpodd : Odd p)
    (hodd : Odd (Nat.card X)) (hcore : pComplCore p X = ⊥)
    (hrank : elementaryAbelianPRank p X ≤ 2) :
    _root_.commutator X ≤ pCore p X ∧ (∃ S : Sylow p X, (S : Subgroup X) = pCore p X) ∧
      IsMulCommutative (X ⧸ pCore p X) ∧ ¬ p ∣ Nat.card (X ⧸ pCore p X) ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q ≤ p :=
  ⟨commutator_le_pCore_of_pComplCore_eq_bot hp hpodd hodd hcore hrank,
    exists_sylow_coe_eq_pCore_of_pComplCore_eq_bot hp hpodd hodd hcore hrank,
    isMulCommutative_quotient_pCore_of_pComplCore_eq_bot hp hpodd hodd hcore hrank,
    not_dvd_card_quotient_pCore_of_pComplCore_eq_bot hp hpodd hodd hcore hrank,
    fun _ hq hqX => prime_le_of_dvd_card_of_pComplCore_eq_bot hp hpodd hodd hcore hrank hq hqX⟩

end

end CFSG.FeitThompson
