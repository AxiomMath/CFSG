module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA
open CFSG.Open (orderBabyMonster orderMonster)
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd sporadicOrdersTable_holds)

theorem not_sq_dvd_of_squarefree {p n : ℕ} (hp : p.Prime) (hn : Squarefree n) :
    ¬ p ^ 2 ∣ n := fun h =>
  hp.one_lt.ne' (Nat.isUnit_iff.1 (hn p (by rw [← sq]; exact h)))

theorem coprime_prime_pow_of_ne {p q : ℕ} (k : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) :
    Nat.Coprime p (q ^ k) :=
  Nat.Coprime.pow_right k ((Nat.coprime_primes hp hq).2 h)

theorem not_sq_dvd_orderBabyMonster_of_eleven_le {p : ℕ} (hp : p.Prime) (h : 11 ≤ p) :
    ¬ p ^ 2 ∣ orderBabyMonster := by
  have hsq : Squarefree (11 * 13 * 17 * 19 * 23 * 31 * 47) := by
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
    norm_num [Nat.primeFactorsList]
  have hA : Nat.Coprime (p ^ 2) (2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2) :=
    Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (Nat.Coprime.mul_right (coprime_prime_pow_of_ne _ hp Nat.prime_two (by omega))
        (coprime_prime_pow_of_ne _ hp Nat.prime_three (by omega)))
      (coprime_prime_pow_of_ne _ hp Nat.prime_five (by omega)))
      (coprime_prime_pow_of_ne _ hp (by norm_num) (by omega)))
  intro hd
  have e : orderBabyMonster =
      (2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2) * (11 * 13 * 17 * 19 * 23 * 31 * 47) := by
    norm_num [orderBabyMonster]
  rw [e] at hd
  exact not_sq_dvd_of_squarefree hp hsq (hA.dvd_of_dvd_mul_left hd)

theorem not_sq_dvd_orderMonster_of_seventeen_le {p : ℕ} (hp : p.Prime) (h : 17 ≤ p) :
    ¬ p ^ 2 ∣ orderMonster := by
  have hsq : Squarefree (17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71) := by
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
    norm_num [Nat.primeFactorsList]
  have hA : Nat.Coprime (p ^ 2) (2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3) :=
    Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (Nat.Coprime.mul_right (Nat.Coprime.mul_right
        (coprime_prime_pow_of_ne _ hp Nat.prime_two (by omega))
        (coprime_prime_pow_of_ne _ hp Nat.prime_three (by omega)))
      (coprime_prime_pow_of_ne _ hp Nat.prime_five (by omega)))
      (coprime_prime_pow_of_ne _ hp (by norm_num) (by omega)))
      (coprime_prime_pow_of_ne _ hp (by norm_num) (by omega)))
      (coprime_prime_pow_of_ne _ hp (by norm_num) (by omega)))
  intro hd
  have e : orderMonster = (2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3) *
      (17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71) := by
    norm_num [orderMonster]
  rw [e] at hd
  exact not_sq_dvd_of_squarefree hp hsq (hA.dvd_of_dvd_mul_left hd)

section Rows

theorem rows_B_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hd : ¬ p ^ 2 ∣ sporOrd .B) :
    I1416Rows.I1416SporRow .B p ∧ I1416QRows.I1416QRow .B p ∧ I1415Rows.I1415Row .B p ∧
      Chev2Rows.CRow .B p := by
  haveI : IsSimpleGroup (NativeSporadic.Carrier .B) := CFSG.Sporadic.B.fam_b_simplicity
  haveI : Finite (NativeSporadic.Carrier .B) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .B (by decide)
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .B
  have hc : Nat.card (NativeSporadic.Carrier .B) = sporOrd .B :=
    (Nat.card_congr b.toEquiv).trans (sporadicOrdersTable_holds .B)
  have hnp : ¬ (sporOrd .B).Prime := by norm_num [sporOrd, orderBabyMonster]
  have hnc := S8.HNRows.exists_noncomm_of_simple (S := NativeSporadic.Carrier .B)
    (by rw [hc]; exact hnp)
  have hd' : ¬ p ^ 2 ∣ Nat.card (NativeSporadic.Carrier .B) := by rw [hc]; exact hd
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  exact ⟨I1416Rows.row_of_model_not_sq_dvd hOut b hnc hp hd',
    I1416QRows.qrow_of_model_not_sq_dvd hOut b hnc hp hd',
    I1415Rows.arow_of_model_not_sq_dvd hOut b hnc hp hd',
    Chev2Rows.crow_of_model_not_sq_dvd hOut b hnc hp hd'⟩

theorem rows_M_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hd : ¬ p ^ 2 ∣ sporOrd .M) :
    I1416Rows.I1416SporRow .M p ∧ I1416QRows.I1416QRow .M p ∧ I1415Rows.I1415Row .M p ∧
      Chev2Rows.CRow .M p := by
  haveI : IsSimpleGroup (NativeSporadic.Carrier .M) := by
    have : IsSimpleGroup CFSG.Open.MonsterY443Derived := CFSG.Milestones.fam_m_simplicity
    exact CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.isSimpleGroup
  haveI : Finite (NativeSporadic.Carrier .M) :=
    CFSG.Sporadic.finite_carrier_M_of_card CFSG.Milestones.fam_m_finiteness
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M
  have hc : Nat.card (NativeSporadic.Carrier .M) = sporOrd .M :=
    (Nat.card_congr b.toEquiv).trans (sporadicOrdersTable_holds .M)
  have hnp : ¬ (sporOrd .M).Prime := by norm_num [sporOrd, orderMonster]
  have hnc := S8.HNRows.exists_noncomm_of_simple (S := NativeSporadic.Carrier .M)
    (by rw [hc]; exact hnp)
  have hd' : ¬ p ^ 2 ∣ Nat.card (NativeSporadic.Carrier .M) := by rw [hc]; exact hd
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  exact ⟨I1416Rows.row_of_model_not_sq_dvd hOut b hnc hp hd',
    I1416QRows.qrow_of_model_not_sq_dvd hOut b hnc hp hd',
    I1415Rows.arow_of_model_not_sq_dvd hOut b hnc hp hd',
    Chev2Rows.crow_of_model_not_sq_dvd hOut b hnc hp hd'⟩

theorem row_B_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hd : ¬ p ^ 2 ∣ sporOrd .B) :
    I1416Rows.I1416SporRow .B p := (rows_B_of_not_sq_dvd hp hd).1

theorem qrow_B_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hd : ¬ p ^ 2 ∣ sporOrd .B) :
    I1416QRows.I1416QRow .B p := (rows_B_of_not_sq_dvd hp hd).2.1

theorem arow_B_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hd : ¬ p ^ 2 ∣ sporOrd .B) :
    I1415Rows.I1415Row .B p := (rows_B_of_not_sq_dvd hp hd).2.2.1

theorem crow_B_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hd : ¬ p ^ 2 ∣ sporOrd .B) :
    Chev2Rows.CRow .B p := (rows_B_of_not_sq_dvd hp hd).2.2.2

theorem row_M_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hd : ¬ p ^ 2 ∣ sporOrd .M) :
    I1416Rows.I1416SporRow .M p := (rows_M_of_not_sq_dvd hp hd).1

theorem qrow_M_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hd : ¬ p ^ 2 ∣ sporOrd .M) :
    I1416QRows.I1416QRow .M p := (rows_M_of_not_sq_dvd hp hd).2.1

theorem arow_M_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hd : ¬ p ^ 2 ∣ sporOrd .M) :
    I1415Rows.I1415Row .M p := (rows_M_of_not_sq_dvd hp hd).2.2.1

theorem crow_M_of_not_sq_dvd {p : ℕ} (hp : p.Prime) (hd : ¬ p ^ 2 ∣ sporOrd .M) :
    Chev2Rows.CRow .M p := (rows_M_of_not_sq_dvd hp hd).2.2.2

theorem row_B_of_eleven_le {p : ℕ} (hp : p.Prime) (h : 11 ≤ p) :
    I1416Rows.I1416SporRow .B p :=
  row_B_of_not_sq_dvd hp (not_sq_dvd_orderBabyMonster_of_eleven_le hp h)

theorem qrow_B_of_eleven_le {p : ℕ} (hp : p.Prime) (h : 11 ≤ p) :
    I1416QRows.I1416QRow .B p :=
  qrow_B_of_not_sq_dvd hp (not_sq_dvd_orderBabyMonster_of_eleven_le hp h)

theorem arow_B_of_eleven_le {p : ℕ} (hp : p.Prime) (h : 11 ≤ p) :
    I1415Rows.I1415Row .B p :=
  arow_B_of_not_sq_dvd hp (not_sq_dvd_orderBabyMonster_of_eleven_le hp h)

theorem crow_B_of_eleven_le {p : ℕ} (hp : p.Prime) (h : 11 ≤ p) :
    Chev2Rows.CRow .B p :=
  crow_B_of_not_sq_dvd hp (not_sq_dvd_orderBabyMonster_of_eleven_le hp h)

theorem row_M_of_seventeen_le {p : ℕ} (hp : p.Prime) (h : 17 ≤ p) :
    I1416Rows.I1416SporRow .M p :=
  row_M_of_not_sq_dvd hp (not_sq_dvd_orderMonster_of_seventeen_le hp h)

theorem qrow_M_of_seventeen_le {p : ℕ} (hp : p.Prime) (h : 17 ≤ p) :
    I1416QRows.I1416QRow .M p :=
  qrow_M_of_not_sq_dvd hp (not_sq_dvd_orderMonster_of_seventeen_le hp h)

theorem arow_M_of_seventeen_le {p : ℕ} (hp : p.Prime) (h : 17 ≤ p) :
    I1415Rows.I1415Row .M p :=
  arow_M_of_not_sq_dvd hp (not_sq_dvd_orderMonster_of_seventeen_le hp h)

theorem crow_M_of_seventeen_le {p : ℕ} (hp : p.Prime) (h : 17 ≤ p) :
    Chev2Rows.CRow .M p :=
  crow_M_of_not_sq_dvd hp (not_sq_dvd_orderMonster_of_seventeen_le hp h)

end Rows

end CFSG.HardMathSupport.Dickson.BMRows
