module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import CFSG.FeitThompson.Local.NormalComplementsPiCoreQuotient
import CFSG.FeitThompson.Local.RankTwoPCoreSeriesAbelianTop
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {p q : ℕ} {X : Type*} [Group X] [Finite X]

private theorem eq_of_prime_dvd_index_pComplCore [Group.IsSolvable X] (hp : p.Prime)
    (hpX : p ∣ Nat.card X) (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → p ≤ q)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2)
    (hq : q.Prime) (hqi : q ∣ (pComplCore p X).index) : q = p := by
  have h1 : p ≤ q := hmin q hq (hqi.trans (Subgroup.index_dvd_card _))
  have h2 : q ≤ p :=
    prime_le_of_dvd_natCard_quotient hp (hodd.of_dvd_nat hpX) hodd hrank hq
      (by rwa [← Subgroup.index_eq_card])
  omega

theorem index_pComplCore_eq_pow_factorization [Group.IsSolvable X] (hp : p.Prime)
    (hpX : p ∣ Nat.card X) (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → p ≤ q)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    (pComplCore p X).index = p ^ (Nat.card X).factorization p := by
  obtain ⟨a, ha⟩ : ∃ a, (pComplCore p X).index = p ^ a :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Subgroup.index_ne_zero_of_finite
      fun hd hdvd => eq_of_prime_dvd_index_pComplCore hp hpX hmin hodd hrank hd hdvd⟩
  have hcard : Nat.card (pComplCore p X) * (pComplCore p X).index = Nat.card X :=
    Subgroup.card_mul_index _
  have hfac : (Nat.card X).factorization p = a := by
    rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite, ha]
    simp [Nat.factorization_eq_zero_of_not_dvd (not_dvd_natCard_pComplCore hp X),
      Nat.Prime.factorization_pow hp]
  rw [hfac, ha]

theorem exists_index_pComplCore_eq_pow [Group.IsSolvable X] (hp : p.Prime)
    (hpX : p ∣ Nat.card X) (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → p ≤ q)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    ∃ a : ℕ, (pComplCore p X).index = p ^ a :=
  ⟨_, index_pComplCore_eq_pow_factorization hp hpX hmin hodd hrank⟩

theorem natCard_range_leftCoset_pComplCore [Group.IsSolvable X] (hp : p.Prime)
    (hpX : p ∣ Nat.card X) (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → p ≤ q)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    Nat.card (Set.range fun g : X => g • (pComplCore p X : Set X))
      = p ^ (Nat.card X).factorization p := by
  rw [natCard_range_leftCoset]
  exact index_pComplCore_eq_pow_factorization hp hpX hmin hodd hrank

theorem isHallPiSubgroup_pComplCore_of_smallest_prime [Group.IsSolvable X] (hp : p.Prime)
    (hpX : p ∣ Nat.card X) (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → p ≤ q)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    IsHallPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} (pComplCore p X) :=
  isHallPiSubgroup_pComplCore hp
    (index_pComplCore_eq_pow_factorization hp hpX hmin hodd hrank)

theorem isHallSubgroup_pComplCore_of_smallest_prime [Group.IsSolvable X] (hp : p.Prime)
    (hpX : p ∣ Nat.card X) (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → p ≤ q)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    IsHallSubgroup ({p}ᶜ : Set ℕ) (pComplCore p X) := by
  have hH := isHallPiSubgroup_pComplCore_of_smallest_prime hp hpX hmin hodd hrank
  refine ⟨isPiSubgroup_iff_isPiNumber.1 (hH.isPiSubgroup.mono fun r hr => hr.2),
    isPiNumber_compl_iff.2 fun r hr => ?_⟩
  have hrp : r = p := by
    by_contra hne
    exact hH.notMem_of_mem_primeFactors_index r hr ⟨Nat.prime_of_mem_primeFactors hr, hne⟩
  simp [hrp]

theorem pComplCore_isNormalHall_of_smallest_prime [Group.IsSolvable X] (hp : p.Prime)
    (hpX : p ∣ Nat.card X) (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → p ≤ q)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    (pComplCore p X).Normal ∧ ¬ p ∣ Nat.card (pComplCore p X) ∧
      ∃ a : ℕ, (pComplCore p X).index = p ^ a :=
  ⟨pComplCore_normal p X, not_dvd_natCard_pComplCore hp X,
    exists_index_pComplCore_eq_pow hp hpX hmin hodd hrank⟩

private theorem minFac_prime_natCard [Nontrivial X] : (Nat.card X).minFac.Prime :=
  Nat.minFac_prime (by have := Finite.one_lt_card (α := X); omega)

theorem pComplCore_minFac_isNormalHall [Group.IsSolvable X] [Nontrivial X]
    (hodd : Odd (Nat.card X))
    (hrank : elementaryAbelianPRank (Nat.card X).minFac X ≤ 2) :
    (pComplCore (Nat.card X).minFac X).Normal ∧
      ¬ (Nat.card X).minFac ∣ Nat.card (pComplCore (Nat.card X).minFac X) ∧
      ∃ a : ℕ, (pComplCore (Nat.card X).minFac X).index = (Nat.card X).minFac ^ a :=
  pComplCore_isNormalHall_of_smallest_prime minFac_prime_natCard (Nat.minFac_dvd _)
    (fun _ hq hqX => Nat.minFac_le_of_dvd hq.two_le hqX) hodd hrank

theorem isHallPiSubgroup_pComplCore_minFac [Group.IsSolvable X] [Nontrivial X]
    (hodd : Odd (Nat.card X))
    (hrank : elementaryAbelianPRank (Nat.card X).minFac X ≤ 2) :
    IsHallPiSubgroup {q : ℕ | q.Prime ∧ q ≠ (Nat.card X).minFac}
      (pComplCore (Nat.card X).minFac X) :=
  isHallPiSubgroup_pComplCore_of_smallest_prime minFac_prime_natCard (Nat.minFac_dvd _)
    (fun _ hq hqX => Nat.minFac_le_of_dvd hq.two_le hqX) hodd hrank

end

end CFSG.FeitThompson
