module

public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import CFSG.FeitThompson.Local.HighRankMaximalPlaneCommutatorPrimePower
public import CFSG.FeitThompson.Local.NondefiningOddPrimesBelowDefining
public import CFSG.FeitThompson.Local.OddRankTwoAutomorphismDerivedPrimePower

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p q n : ℕ} {P : Type*} [Group P]

theorem maximal_isMulCommutative_pow_eq_one_of_maximal_isElementaryAbelianSubgroup
    {E : Subgroup P} (h : Maximal (IsElementaryAbelianSubgroup p) E) :
    Maximal (fun A : Subgroup P => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E :=
  ⟨⟨h.prop.isMulCommutative, h.prop.pow_eq_one⟩,
    fun _ hB hle => h.le_of_ge (isElementaryAbelianSubgroup_iff.2 hB) hle⟩

theorem isPGroup_commutator_subgroup_of_odd_aut_of_isPNarrow [Finite P] (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) (hnarrow : IsPNarrow p P) {A : Subgroup (MulAut P)}
    (hA : Odd (Nat.card ↥A)) : IsPGroup p ↥(⁅A, A⁆ : Subgroup (MulAut P)) := by
  rcases le_or_gt (elementaryAbelianPRank p P) 2 with hrank | hrank
  · exact isPGroup_commutator_subgroup_of_odd_aut_of_elementaryAbelianPRank_le_two hp hodd hP
      hrank hA
  · obtain ⟨E, hE, hplane⟩ := ((isPNarrow_iff p P).1 hnarrow).resolve_left (by omega)
    exact isPGroup_commutator_of_maximal_plane hp hodd hP
      (maximal_isMulCommutative_pow_eq_one_of_maximal_isElementaryAbelianSubgroup hE) hplane
      (by omega) A

theorem isPGroup_commutator_of_odd_aut_of_isPNarrow [Finite P] (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) (hnarrow : IsPNarrow p P) {A : Subgroup (MulAut P)}
    (hA : Odd (Nat.card ↥A)) : IsPGroup p ↥(_root_.commutator ↥A) := by
  have h := isPGroup_commutator_subgroup_of_odd_aut_of_isPNarrow hp hodd hP hnarrow hA
  rw [← Subgroup.map_subtype_commutator] at h
  exact h.of_equiv
    (((_root_.commutator ↥A).equivMapOfInjective A.subtype A.subtype_injective).symm)

theorem prime_lt_of_dvd_natCard_of_odd_aut_of_isPNarrow [Finite P] (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) (hnarrow : IsPNarrow p P) {A : Subgroup (MulAut P)}
    (hA : Odd (Nat.card ↥A)) (hq : q.Prime) (hqp : q ≠ p) (hqA : q ∣ Nat.card ↥A) : q < p := by
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hodd
    have := hp.two_le
    omega
  rcases le_or_gt (elementaryAbelianPRank p P) 2 with hrank | hrank
  · exact prime_lt_of_dvd_card_of_odd_of_elementaryAbelianPRank_le_two hp hodd hP hrank hA hq hqp
      hqA
  · obtain ⟨E, hE, hplane⟩ := ((isPNarrow_iff p P).1 hnarrow).resolve_left (by omega)
    have h := prime_dvd_sub_one_of_dvd_natCard_of_maximal_plane hp hodd hP
      (maximal_isMulCommutative_pow_eq_one_of_maximal_isElementaryAbelianSubgroup hE) hplane
      (by omega) hq hqp hqA
    have := Nat.le_of_dvd (by omega) h
    omega

theorem commutator_isPGroup_and_prime_lt_of_odd_aut_of_isPNarrow [Finite P] (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) (hnarrow : IsPNarrow p P) {A : Subgroup (MulAut P)}
    (hA : Odd (Nat.card ↥A)) :
    IsPGroup p ↥(⁅A, A⁆ : Subgroup (MulAut P)) ∧
      ∀ q : ℕ, q.Prime → q ≠ p → q ∣ Nat.card ↥A → q < p :=
  ⟨isPGroup_commutator_subgroup_of_odd_aut_of_isPNarrow hp hodd hP hnarrow hA,
    fun _ hq hqp hqA =>
      prime_lt_of_dvd_natCard_of_odd_aut_of_isPNarrow hp hodd hP hnarrow hA hq hqp hqA⟩

theorem commutator_isPGroup_and_prime_lt_of_odd_aut_of_card_eq_pow (hp : p.Prime) (hodd : Odd p)
    (hcard : Nat.card P = p ^ n) (hnarrow : IsPNarrow p P) {A : Subgroup (MulAut P)}
    (hA : Odd (Nat.card ↥A)) :
    (∃ a : ℕ, Nat.card ↥(⁅A, A⁆ : Subgroup (MulAut P)) = p ^ a) ∧
      ∀ q : ℕ, q.Prime → q ≠ p → q ∣ Nat.card ↥A → q < p := by
  have := Fact.mk hp
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨h1, h2⟩ := commutator_isPGroup_and_prime_lt_of_odd_aut_of_isPNarrow hp hodd
    (IsPGroup.of_card hcard) hnarrow hA
  exact ⟨IsPGroup.iff_card.1 h1, h2⟩

end

end CFSG.FeitThompson
