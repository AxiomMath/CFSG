module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Local.PLengthOneNormalSeries
import CFSG.FeitThompson.Local.RankTwoTrivialPprimeCoreAbelianQuotient
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Foundations.SolvableHallExistence

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open QuotientGroup Subgroup Pointwise

variable {p q : ℕ} {X : Type*} [Group X] [Finite X]

noncomputable def quotientPComplPCoreEquiv (p : ℕ) (X : Type*) [Group X] [Finite X] :
    X ⧸ pComplPCore p X ≃* (X ⧸ pComplCore p X) ⧸ pCore p (X ⧸ pComplCore p X) :=
  (QuotientGroup.quotientMulEquivOfEq (M := pComplPCore p X)
    (N := ((mk' (pCore p (X ⧸ pComplCore p X))).comp (mk' (pComplCore p X))).ker)
    (by rw [← MonoidHom.comap_ker, ker_mk', pComplPCore_eq_comap])).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        ((mk'_surjective _).comp (mk'_surjective _)))

@[simp]
theorem quotientPComplPCoreEquiv_mk (p : ℕ) (X : Type*) [Group X] [Finite X] (x : X) :
    quotientPComplPCoreEquiv p X (mk x) = mk (mk x) := (rfl)

theorem natCard_quotient_pComplPCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    Nat.card (X ⧸ pComplPCore p X) =
      Nat.card ((X ⧸ pComplCore p X) ⧸ pCore p (X ⧸ pComplCore p X)) :=
  Nat.card_congr (quotientPComplPCoreEquiv p X).toEquiv

private theorem coprime_natCard_pComplCore (hp : p.Prime) (X : Type*) [Group X] [Finite X] :
    p.Coprime (Nat.card (pComplCore p X)) :=
  hp.coprime_iff_not_dvd.2 (not_dvd_natCard_pComplCore hp X)

private theorem elementaryAbelianPRank_quotient_pComplCore_le_two (hp : p.Prime)
    (X : Type*) [Group X] [Finite X] (hrank : elementaryAbelianPRank p X ≤ 2) :
    elementaryAbelianPRank p (X ⧸ pComplCore p X) ≤ 2 :=
  (elementaryAbelianPRank_quotient_eq hp (coprime_natCard_pComplCore hp X)).trans_le hrank

theorem isMulCommutative_quotient_pComplPCore [Group.IsSolvable X] (hp : p.Prime) (hpodd : Odd p)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    IsMulCommutative (X ⧸ pComplPCore p X) :=
  have : Group.IsSolvable (X ⧸ pComplCore p X) := Group.isSolvable_of_surjective (mk'_surjective _)
  have := isMulCommutative_quotient_pCore_of_pComplCore_eq_bot (X := X ⧸ pComplCore p X) hp hpodd
    (odd_natCard_quotient _ hodd) (pComplCore_quotient_pComplCore p X)
    (elementaryAbelianPRank_quotient_pComplCore_le_two hp X hrank)
  isMulCommutative_of_mulEquiv (quotientPComplPCoreEquiv p X)

theorem not_dvd_natCard_quotient_pComplPCore [Group.IsSolvable X] (hp : p.Prime) (hpodd : Odd p)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    ¬ p ∣ Nat.card (X ⧸ pComplPCore p X) := by
  have : Group.IsSolvable (X ⧸ pComplCore p X) := Group.isSolvable_of_surjective (mk'_surjective _)
  rw [natCard_quotient_pComplPCore]
  exact not_dvd_card_quotient_pCore_of_pComplCore_eq_bot (X := X ⧸ pComplCore p X) hp hpodd
    (odd_natCard_quotient _ hodd) (pComplCore_quotient_pComplCore p X)
    (elementaryAbelianPRank_quotient_pComplCore_le_two hp X hrank)

theorem coprime_natCard_quotient_pComplPCore [Group.IsSolvable X] (hp : p.Prime) (hpodd : Odd p)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    Nat.Coprime (Nat.card (X ⧸ pComplPCore p X)) p :=
  ((hp.coprime_iff_not_dvd).2
    (not_dvd_natCard_quotient_pComplPCore hp hpodd hodd hrank)).symm

theorem pComplPCore_eq_sup_of_sylow [Group.IsSolvable X] (hp : p.Prime) (hpodd : Odd p)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) (P : Sylow p X) :
    pComplPCore p X = pComplCore p X ⊔ (P : Subgroup X) := by
  have := Fact.mk hp
  have : Group.IsSolvable (X ⧸ pComplCore p X) := Group.isSolvable_of_surjective (mk'_surjective _)
  set N := pComplCore p X
  have hcop : p.Coprime (Nat.card N) := coprime_natCard_pComplCore hp X
  have hPcard : Nat.card (P : Subgroup X) = p ^ (Nat.card X).factorization p :=
    P.card_eq_multiplicity
  have hS : Nat.card (((P : Subgroup X) ⊔ N).map (mk' N) : Subgroup (X ⧸ N))
      = p ^ (Nat.card (X ⧸ N)).factorization p :=
    natCard_map_sup_mk'_eq_pow_factorization hp hcop hPcard
  obtain ⟨Q, hQ⟩ := exists_sylow_coe_eq_pCore_of_pComplCore_eq_bot (X := X ⧸ N) hp hpodd
    (odd_natCard_quotient _ hodd) (pComplCore_quotient_pComplCore p X)
    (elementaryAbelianPRank_quotient_pComplCore_le_two hp X hrank)
  have hQnormal : (Q : Subgroup (X ⧸ N)).Normal := by
    rw [hQ]; exact Subgroup.normal_of_characteristic _
  have := Sylow.unique_of_normal Q hQnormal
  have hmap : (((P : Subgroup X) ⊔ N).map (mk' N) : Subgroup (X ⧸ N)) = pCore p (X ⧸ N) := by
    rw [← hQ, ← Sylow.coe_ofCard _ hS]
    exact congrArg _ (Subsingleton.elim _ _)
  have hker : (mk' N).ker ≤ (P : Subgroup X) ⊔ N := by rw [ker_mk']; exact le_sup_right
  rw [pComplPCore_eq_comap, ← hmap, Subgroup.comap_map_eq_self hker, sup_comm]

theorem coe_pComplPCore_eq_mul_of_sylow [Group.IsSolvable X] (hp : p.Prime) (hpodd : Odd p)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) (P : Sylow p X) :
    (pComplPCore p X : Set X) = (pComplCore p X : Set X) * (P : Subgroup X) := by
  rw [pComplPCore_eq_sup_of_sylow hp hpodd hodd hrank P, Subgroup.normal_mul]

theorem le_pComplPCore_of_sylow [Group.IsSolvable X] (hp : p.Prime) (hpodd : Odd p)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) (P : Sylow p X) :
    (P : Subgroup X) ≤ pComplPCore p X := by
  rw [pComplPCore_eq_sup_of_sylow hp hpodd hodd hrank P]
  exact le_sup_right

theorem prime_le_of_dvd_natCard_quotient [Group.IsSolvable X] (hp : p.Prime) (hpodd : Odd p)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) (hq : q.Prime)
    (hqX : q ∣ Nat.card (X ⧸ pComplCore p X)) : q ≤ p :=
  have : Group.IsSolvable (X ⧸ pComplCore p X) := Group.isSolvable_of_surjective (mk'_surjective _)
  prime_le_of_dvd_card_of_pComplCore_eq_bot (X := X ⧸ pComplCore p X) hp hpodd
    (odd_natCard_quotient _ hodd) (pComplCore_quotient_pComplCore p X)
    (elementaryAbelianPRank_quotient_pComplCore_le_two hp X hrank) hq hqX

theorem rank_two_pComplPCore_series [Group.IsSolvable X] (hp : p.Prime) (hpodd : Odd p)
    (hodd : Odd (Nat.card X)) (hrank : elementaryAbelianPRank p X ≤ 2) :
    IsMulCommutative (X ⧸ pComplPCore p X) ∧ ¬ p ∣ Nat.card (X ⧸ pComplPCore p X) ∧
      (∀ P : Sylow p X, pComplPCore p X = pComplCore p X ⊔ (P : Subgroup X)) ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card (X ⧸ pComplCore p X) → q ≤ p :=
  ⟨isMulCommutative_quotient_pComplPCore hp hpodd hodd hrank,
    not_dvd_natCard_quotient_pComplPCore hp hpodd hodd hrank,
    fun P => pComplPCore_eq_sup_of_sylow hp hpodd hodd hrank P,
    fun _ hq hqX => prime_le_of_dvd_natCard_quotient hp hpodd hodd hrank hq hqX⟩

end

end CFSG.FeitThompson
