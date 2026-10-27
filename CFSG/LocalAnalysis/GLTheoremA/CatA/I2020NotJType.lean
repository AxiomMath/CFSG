module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05NonIso
public import CFSG.GroupTheory.PrimitiveDivisorOrders
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLieChar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremA.YS05NonIso
  CFSG.ComponentClassification.HarrisLit.T1.P51e
  CFSG.ComponentClassification.HarrisLit.T1.P51e.IsPrimDiv

@[expose] def NotJTypeTag (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSL ∧ n = 2) ∨ (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaPlus ∧ n = 4) ∨
    (t = .POmegaMinus ∧ n = 4) ∨ t = .G2 ∨ t = .trialityD4

theorem lieOrderNumerator_PSL_two (x : ℕ) : lieOrderNumerator .PSL 2 x = x * (x ^ 2 - 1) := by
  have hprod : (∏ i ∈ Finset.Icc 2 2, (x ^ i - 1)) = (x ^ 2 - 1) := by simp
  simp only [lieOrderNumerator]
  rw [hprod]
  norm_num

private lemma num_POmegaPlus (x : ℕ) : lieOrderNumerator .POmegaPlus 4 x =
    x ^ 12 * ((x ^ 4 - 1) * ((x ^ 2 - 1) * (x ^ 4 - 1) * (x ^ 6 - 1))) := by
  have hprod : (∏ i ∈ Finset.Icc 1 3, (x ^ (2 * i) - 1)) =
      (x ^ 2 - 1) * (x ^ 4 - 1) * (x ^ 6 - 1) := by
    simp [Finset.prod_Icc_succ_top]
  simp only [lieOrderNumerator]
  rw [hprod]
  ring_nf

private lemma num_POmegaMinus (x : ℕ) : lieOrderNumerator .POmegaMinus 4 x =
    x ^ 12 * ((x ^ 4 + 1) * ((x ^ 2 - 1) * (x ^ 4 - 1) * (x ^ 6 - 1))) := by
  have hprod : (∏ i ∈ Finset.Icc 1 3, (x ^ (2 * i) - 1)) =
      (x ^ 2 - 1) * (x ^ 4 - 1) * (x ^ 6 - 1) := by
    simp [Finset.prod_Icc_succ_top]
  simp only [lieOrderNumerator]
  rw [hprod]
  ring_nf

private lemma num_G2 (n x : ℕ) : lieOrderNumerator .G2 n x =
    x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) := by
  simp only [lieOrderNumerator]
  ring

private lemma num_trialityD4 (n x : ℕ) : lieOrderNumerator .trialityD4 n x =
    x ^ 12 * ((x ^ 8 + x ^ 4 + 1) * ((x ^ 6 - 1) * (x ^ 2 - 1))) := by
  simp only [lieOrderNumerator]
  ring

private lemma goodFactor_POmegaOdd {q a M : ℕ} (ha : 0 < a) (hM : 6 * a < M) :
    GoodFactor q M (q ^ (9 * a) * ((q ^ (2 * a) - 1) * (q ^ (4 * a) - 1) *
      (q ^ (6 * a) - 1))) := by
  exact GoodFactor.mul (q := q) (M := M) (GoodFactor.pow (q := q) (M := M) (9 * a))
    (GoodFactor.mul (q := q) (M := M)
      (GoodFactor.mul (q := q) (M := M)
        (GoodFactor.sub (q := q) (M := M) (2 * a) (by omega) (by omega))
        (GoodFactor.sub (q := q) (M := M) (4 * a) (by omega) (by omega)))
      (GoodFactor.sub (q := q) (M := M) (6 * a) (by omega) hM))

private lemma goodFactor_POmegaPlus {q a M : ℕ} (ha : 0 < a) (hM : 6 * a < M) :
    GoodFactor q M (q ^ (12 * a) * ((q ^ (4 * a) - 1) *
      ((q ^ (2 * a) - 1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1)))) := by
  exact GoodFactor.mul (q := q) (M := M) (GoodFactor.pow (q := q) (M := M) (12 * a))
    (GoodFactor.mul (q := q) (M := M)
      (GoodFactor.sub (q := q) (M := M) (4 * a) (by omega) (by omega))
      (GoodFactor.mul (q := q) (M := M)
        (GoodFactor.mul (q := q) (M := M)
          (GoodFactor.sub (q := q) (M := M) (2 * a) (by omega) (by omega))
          (GoodFactor.sub (q := q) (M := M) (4 * a) (by omega) (by omega)))
        (GoodFactor.sub (q := q) (M := M) (6 * a) (by omega) hM)))

private lemma goodFactor_POmegaMinus {q a M : ℕ} (ha : 0 < a) (hM : 8 * a < M) :
    GoodFactor q M (q ^ (12 * a) * ((q ^ (4 * a) + 1) *
      ((q ^ (2 * a) - 1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1)))) := by
  exact GoodFactor.mul (q := q) (M := M) (GoodFactor.pow (q := q) (M := M) (12 * a))
    (GoodFactor.mul (q := q) (M := M)
      (GoodFactor.add (q := q) (M := M) (4 * a) (by omega) (by omega))
      (GoodFactor.mul (q := q) (M := M)
        (GoodFactor.mul (q := q) (M := M)
          (GoodFactor.sub (q := q) (M := M) (2 * a) (by omega) (by omega))
          (GoodFactor.sub (q := q) (M := M) (4 * a) (by omega) (by omega)))
        (GoodFactor.sub (q := q) (M := M) (6 * a) (by omega) (by omega))))

private lemma goodFactor_G2 {q a M : ℕ} (ha : 0 < a) (hM : 6 * a < M) :
    GoodFactor q M (q ^ (6 * a) * ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1))) := by
  exact GoodFactor.mul (q := q) (M := M) (GoodFactor.pow (q := q) (M := M) (6 * a))
    (GoodFactor.mul (q := q) (M := M)
      (GoodFactor.sub (q := q) (M := M) (6 * a) (by omega) hM)
      (GoodFactor.sub (q := q) (M := M) (2 * a) (by omega) (by omega)))

private lemma goodFactor_trialityD4 {q a M : ℕ} (ha : 0 < a) (hM : 12 * a < M) :
    GoodFactor q M (q ^ (12 * a) * ((q ^ (8 * a) + q ^ (4 * a) + 1) *
      ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1)))) := by
  exact GoodFactor.mul (q := q) (M := M) (GoodFactor.pow (q := q) (M := M) (12 * a))
    (GoodFactor.mul (q := q) (M := M)
      (GoodFactor.triality (q := q) (M := M) a ha hM)
      (GoodFactor.mul (q := q) (M := M)
        (GoodFactor.sub (q := q) (M := M) (6 * a) (by omega) (by omega))
        (GoodFactor.sub (q := q) (M := M) (2 * a) (by omega) (by omega))))

private lemma goodFactor_A2 {q b M : ℕ} (hb : 0 < b) (hM : 3 * b < M) :
    GoodFactor q M (q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) - 1))) := by
  exact GoodFactor.mul (q := q) (M := M) (GoodFactor.pow (q := q) (M := M) (3 * b))
    (GoodFactor.mul (q := q) (M := M)
      (GoodFactor.sub (q := q) (M := M) (2 * b) (by omega) (by omega))
      (GoodFactor.sub (q := q) (M := M) (3 * b) (by omega) hM))

private lemma goodFactor_B2 {q b M : ℕ} (hb : 0 < b) (hM : 4 * b < M) :
    GoodFactor q M (q ^ (4 * b) * ((q ^ (2 * b) - 1) * (q ^ (4 * b) - 1))) := by
  exact GoodFactor.mul (q := q) (M := M) (GoodFactor.pow (q := q) (M := M) (4 * b))
    (GoodFactor.mul (q := q) (M := M)
      (GoodFactor.sub (q := q) (M := M) (2 * b) (by omega) (by omega))
      (GoodFactor.sub (q := q) (M := M) (4 * b) (by omega) hM))

private lemma goodFactor_A3 {q b M : ℕ} (hb : 0 < b) (hM : 4 * b < M) :
    GoodFactor q M (q ^ (6 * b) * ((q ^ (2 * b) - 1) *
      ((q ^ (3 * b) - 1) * (q ^ (4 * b) - 1)))) := by
  exact GoodFactor.mul (q := q) (M := M) (GoodFactor.pow (q := q) (M := M) (6 * b))
    (GoodFactor.mul (q := q) (M := M)
      (GoodFactor.sub (q := q) (M := M) (2 * b) (by omega) (by omega))
      (GoodFactor.mul (q := q) (M := M)
        (GoodFactor.sub (q := q) (M := M) (3 * b) (by omega) (by omega))
        (GoodFactor.sub (q := q) (M := M) (4 * b) (by omega) hM)))

private lemma goodFactor_U4 {q b M : ℕ} (hb : 0 < b) (hM : 6 * b < M) :
    GoodFactor q M (q ^ (6 * b) * ((q ^ (2 * b) - 1) *
      ((q ^ (3 * b) + 1) * (q ^ (4 * b) - 1)))) := by
  exact GoodFactor.mul (q := q) (M := M) (GoodFactor.pow (q := q) (M := M) (6 * b))
    (GoodFactor.mul (q := q) (M := M)
      (GoodFactor.sub (q := q) (M := M) (2 * b) (by omega) (by omega))
      (GoodFactor.mul (q := q) (M := M)
        (GoodFactor.add (q := q) (M := M) (3 * b) (by omega) (by omega))
        (GoodFactor.sub (q := q) (M := M) (4 * b) (by omega) (by omega))))

private lemma exists_prim_PSL2 {q a : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (ha : 0 < a)
    (hm : 3 ≤ 2 * a) :
    ∃ r : ℕ, IsPrimDiv r q (2 * a) ∧ r ∣ q ^ a * (q ^ (2 * a) - 1) ∧ ¬ r ∣ 2 := by
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) hm
  have hr2 := hr.ne_two (hq.odd_of_ne_two hq2) (by omega)
  exact ⟨r, hr, dvd_mul_of_dvd_right hr.2.1 _, hr.not_dvd_small hq.pos (by omega : 4 ≤ 2 * a)
      (by norm_num) (by norm_num)⟩

private lemma exists_prim_U3 {q b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hb : 0 < b)
    (hm : 3 ≤ 6 * b) :
    ∃ r : ℕ, IsPrimDiv r q (6 * b) ∧
      r ∣ q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) + 1)) ∧
      ¬ r ∣ Nat.gcd 3 (q ^ b + 1) := by
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) hm
  have hr2 := hr.ne_two (hq.odd_of_ne_two hq2) (by omega)
  have hfac : q ^ (6 * b) - 1 = (q ^ (3 * b) - 1) * (q ^ (3 * b) + 1) := by
    rw [show q ^ (6 * b) = (q ^ (3 * b)) ^ 2 by rw [show 6 * b = 3 * b * 2 by ring, pow_mul]]
    rw [show (1 : ℕ) = 1 ^ 2 by norm_num, Nat.sq_sub_sq]
    ring
  have hnot : ¬ r ∣ q ^ (3 * b) - 1 := hr.2.2 (3 * b) (by omega) (by omega)
  have hplus : r ∣ q ^ (3 * b) + 1 := by
    rcases hr.1.dvd_mul.mp (hfac ▸ hr.2.1) with h | h
    · exact absurd h hnot
    · exact h
  refine ⟨r, hr, ?_, ?_⟩
  · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hplus _) _
  · intro hd
    have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr.1 Nat.prime_three).mp
      (hd.trans (Nat.gcd_dvd_left 3 _))
    have hb1 : r ∣ q ^ b + 1 := hd.trans (Nat.gcd_dvd_right 3 _)
    have h2 : r ∣ q ^ (2 * b) - 1 := by
      have e : q ^ (2 * b) - 1 = (q ^ b - 1) * (q ^ b + 1) := by
        rw [show q ^ (2 * b) = (q ^ b) ^ 2 by rw [show 2 * b = b * 2 by ring, pow_mul]]
        rw [show (1 : ℕ) = 1 ^ 2 by norm_num, Nat.sq_sub_sq]
        ring
      rw [e]
      exact dvd_mul_of_dvd_right hb1 _
    exact (hr.2.2 (2 * b) (by omega) (by omega)) (by simpa [hr3] using h2)

private lemma exists_prim_G2 {q a : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (ha : 0 < a)
    (hm : 3 ≤ 6 * a) :
    ∃ r : ℕ, IsPrimDiv r q (6 * a) ∧
      r ∣ q ^ (6 * a) * ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1)) ∧ ¬ r ∣ 1 := by
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) hm
  refine ⟨r, hr, ?_, fun hd => hr.1.one_lt.ne' (Nat.dvd_one.mp hd)⟩
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hr.2.1 (q ^ (2 * a) - 1)) (q ^ (6 * a))

private lemma exists_prim_trialityD4 {q a : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (ha : 0 < a)
    (hm : 3 ≤ 12 * a) (hqpos : 0 < q) :
    ∃ r : ℕ, IsPrimDiv r q (12 * a) ∧
      r ∣ q ^ (12 * a) * ((q ^ (8 * a) + q ^ (4 * a) + 1) *
        ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1))) ∧ ¬ r ∣ 1 := by
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) hm
  have hfac : q ^ (12 * a) - 1 = (q ^ (4 * a) - 1) * (q ^ (8 * a) + q ^ (4 * a) + 1) := by
    simpa [show 2 * (4 * a) = 8 * a by ring, show 3 * (4 * a) = 12 * a by ring]
      using pow_three_mul_sub_one hqpos (m := 4 * a)
  have hnot : ¬ r ∣ q ^ (4 * a) - 1 := hr.2.2 (4 * a) (by omega) (by omega)
  have htri : r ∣ q ^ (8 * a) + q ^ (4 * a) + 1 := by
    rcases hr.1.dvd_mul.mp (hfac ▸ hr.2.1) with h | h
    · exact absurd h hnot
    · exact h
  refine ⟨r, hr, ?_, fun hd => hr.1.one_lt.ne' (Nat.dvd_one.mp hd)⟩
  exact dvd_mul_of_dvd_right
    (dvd_mul_of_dvd_left htri ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1))) (q ^ (12 * a))

private lemma exists_prim_A2 {q b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hb : 0 < b)
    (hm : 3 ≤ 3 * b) :
    ∃ r : ℕ, IsPrimDiv r q (3 * b) ∧
      r ∣ q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) - 1)) ∧
      ¬ r ∣ Nat.gcd 3 (q ^ b - 1) := by
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) hm
  refine ⟨r, hr, ?_, ?_⟩
  · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hr.2.1 (q ^ (2 * b) - 1)) (q ^ (3 * b))
  · intro hd
    have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr.1 Nat.prime_three).mp
      (hd.trans (Nat.gcd_dvd_left 3 _))
    have hb1 : r ∣ q ^ b - 1 := hd.trans (Nat.gcd_dvd_right 3 _)
    exact (hr.2.2 b hb (by omega)) (by simpa [hr3] using hb1)

private lemma exists_prim_B2 {q b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hb : 0 < b)
    (hm : 3 ≤ 4 * b) :
    ∃ r : ℕ, IsPrimDiv r q (4 * b) ∧
      r ∣ q ^ (4 * b) * ((q ^ (2 * b) - 1) * (q ^ (4 * b) - 1)) ∧
      ¬ r ∣ Nat.gcd 2 (q ^ b - 1) := by
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) hm
  have hr2 := hr.ne_two (hq.odd_of_ne_two hq2) (by omega)
  refine ⟨r, hr, ?_, fun hd => hr.not_dvd_small hq.pos (by omega : 4 ≤ 4 * b) (by norm_num) (by
      norm_num) (hd.trans (Nat.gcd_dvd_left 2 _))⟩
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hr.2.1 (q ^ (2 * b) - 1)) (q ^ (4 * b))

private lemma exists_prim_A3 {q b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hb : 0 < b)
    (hm : 3 ≤ 4 * b) :
    ∃ r : ℕ, IsPrimDiv r q (4 * b) ∧
      r ∣ q ^ (6 * b) * ((q ^ (2 * b) - 1) *
        ((q ^ (3 * b) - 1) * (q ^ (4 * b) - 1))) ∧
      ¬ r ∣ Nat.gcd 4 (q ^ b - 1) := by
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) hm
  have hr2 := hr.ne_two (hq.odd_of_ne_two hq2) (by omega)
  refine ⟨r, hr, ?_, fun hd => hr.not_dvd_small hq.pos (by omega : 4 ≤ 4 * b) (by norm_num) (by
      norm_num) (hd.trans (Nat.gcd_dvd_left 4 _))⟩
  exact dvd_mul_of_dvd_right
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hr.2.1 (q ^ (3 * b) - 1))
      (q ^ (2 * b) - 1)) (q ^ (6 * b))

private lemma exists_prim_U4 {q b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hb : 0 < b)
    (hm : 3 ≤ 6 * b) :
    ∃ r : ℕ, IsPrimDiv r q (6 * b) ∧
      r ∣ q ^ (6 * b) * ((q ^ (2 * b) - 1) *
        ((q ^ (3 * b) + 1) * (q ^ (4 * b) - 1))) ∧
      ¬ r ∣ Nat.gcd 4 (q ^ b + 1) := by
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) hm
  have hr2 := hr.ne_two (hq.odd_of_ne_two hq2) (by omega)
  have hfac : q ^ (6 * b) - 1 = (q ^ (3 * b) - 1) * (q ^ (3 * b) + 1) := by
    simpa [show 2 * (3 * b) = 6 * b by ring] using pow_two_mul_sub_one q (3 * b)
  have hnot : ¬ r ∣ q ^ (3 * b) - 1 := hr.2.2 (3 * b) (by omega) (by omega)
  have hplus : r ∣ q ^ (3 * b) + 1 := by
    rcases hr.1.dvd_mul.mp (hfac ▸ hr.2.1) with h | h
    · exact absurd h hnot
    · exact h
  refine ⟨r, hr, ?_, fun hd => hr.not_dvd_small hq.pos (by omega : 4 ≤ 6 * b) (by norm_num) (by
      norm_num) (hd.trans (Nat.gcd_dvd_left 4 _))⟩
  exact dvd_mul_of_dvd_right
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hplus (q ^ (4 * b) - 1))
      (q ^ (2 * b) - 1)) (q ^ (6 * b))

private lemma no_L2_A2 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 1 * a = 3 * b)
    (E1 : M * 2 = q ^ a * (q ^ (2 * a) - 1))
    (E2 : M * Nat.gcd 3 (q ^ b - 1) = q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) - 1))) :
        False := by
  have hlt : 3 * b < 2 * a := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_PSL2 hq hq2 ha (by omega)
  exact no_order_eq_of_primitive_divisor E1 E2 hr hrN hrd hq.pos (by omega)
    (goodFactor_A2 (M := 2 * a) hb hlt)

private lemma no_L2_B2 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 1 * a = 4 * b)
    (E1 : M * 2 = q ^ a * (q ^ (2 * a) - 1))
    (E2 : M * Nat.gcd 2 (q ^ b - 1) = q ^ (4 * b) * ((q ^ (2 * b) - 1) * (q ^ (4 * b) - 1))) :
        False := by
  have hlt : 4 * b < 2 * a := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_PSL2 hq hq2 ha (by omega)
  exact no_order_eq_of_primitive_divisor E1 E2 hr hrN hrd hq.pos (by omega)
    (goodFactor_B2 (M := 2 * a) hb hlt)

private lemma no_L2_A3 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 1 * a = 6 * b)
    (E1 : M * 2 = q ^ a * (q ^ (2 * a) - 1))
    (E2 : M * Nat.gcd 4 (q ^ b - 1) = q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) - 1) * (q
        ^ (4 * b) - 1)))) : False := by
  have hlt : 4 * b < 2 * a := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_PSL2 hq hq2 ha (by omega)
  exact no_order_eq_of_primitive_divisor E1 E2 hr hrN hrd hq.pos (by omega)
    (goodFactor_A3 (M := 2 * a) hb hlt)

private lemma no_L2_U4 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 1 * a = 6 * b)
    (E1 : M * 2 = q ^ a * (q ^ (2 * a) - 1))
    (E2 : M * Nat.gcd 4 (q ^ b + 1) = q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) + 1) * (q
        ^ (4 * b) - 1)))) : False := by
  have hlt : 6 * b < 2 * a := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_PSL2 hq hq2 ha (by omega)
  exact no_order_eq_of_primitive_divisor E1 E2 hr hrN hrd hq.pos (by omega)
    (goodFactor_U4 (M := 2 * a) hb hlt)

private lemma no_OmegaOdd_A2 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 9 * a = 3 * b)
    (E1 : M * 2 = q ^ (9 * a) * ((q ^ (2 * a) - 1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1)))
    (E2 : M * Nat.gcd 3 (q ^ b - 1) = q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) - 1))) :
        False := by
  have hlt : 6 * a < 3 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_A2 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaOdd (M := 3 * b) ha hlt)

private lemma no_OmegaOdd_U3 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 9 * a = 3 * b)
    (E1 : M * 2 = q ^ (9 * a) * ((q ^ (2 * a) - 1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1)))
    (E2 : M * Nat.gcd 3 (q ^ b + 1) = q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) + 1))) :
        False := by
  have hlt : 6 * a < 6 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_U3 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaOdd (M := 6 * b) ha hlt)

private lemma no_OmegaOdd_B2 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 9 * a = 4 * b)
    (E1 : M * 2 = q ^ (9 * a) * ((q ^ (2 * a) - 1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1)))
    (E2 : M * Nat.gcd 2 (q ^ b - 1) = q ^ (4 * b) * ((q ^ (2 * b) - 1) * (q ^ (4 * b) - 1))) :
        False := by
  have hlt : 6 * a < 4 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_B2 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaOdd (M := 4 * b) ha hlt)

private lemma no_OmegaOdd_U4 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 9 * a = 6 * b)
    (E1 : M * 2 = q ^ (9 * a) * ((q ^ (2 * a) - 1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1)))
    (E2 : M * Nat.gcd 4 (q ^ b + 1) = q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) + 1) * (q
        ^ (4 * b) - 1)))) : False := by
  have hlt : 6 * a < 6 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_U4 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaOdd (M := 6 * b) ha hlt)

private lemma no_OmegaPlus_A2 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 3 * b)
    (E1 : M * Nat.gcd 4 (q ^ (4 * a) - 1) = q ^ (12 * a) * ((q ^ (4 * a) - 1) * ((q ^ (2 * a) -
        1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1))))
    (E2 : M * Nat.gcd 3 (q ^ b - 1) = q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) - 1))) :
        False := by
  have hlt : 6 * a < 3 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_A2 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaPlus (M := 3 * b) ha hlt)

private lemma no_OmegaPlus_U3 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 3 * b)
    (E1 : M * Nat.gcd 4 (q ^ (4 * a) - 1) = q ^ (12 * a) * ((q ^ (4 * a) - 1) * ((q ^ (2 * a) -
        1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1))))
    (E2 : M * Nat.gcd 3 (q ^ b + 1) = q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) + 1))) :
        False := by
  have hlt : 6 * a < 6 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_U3 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaPlus (M := 6 * b) ha hlt)

private lemma no_OmegaPlus_B2 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 4 * b)
    (E1 : M * Nat.gcd 4 (q ^ (4 * a) - 1) = q ^ (12 * a) * ((q ^ (4 * a) - 1) * ((q ^ (2 * a) -
        1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1))))
    (E2 : M * Nat.gcd 2 (q ^ b - 1) = q ^ (4 * b) * ((q ^ (2 * b) - 1) * (q ^ (4 * b) - 1))) :
        False := by
  have hlt : 6 * a < 4 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_B2 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaPlus (M := 4 * b) ha hlt)

private lemma no_OmegaPlus_A3 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 6 * b)
    (E1 : M * Nat.gcd 4 (q ^ (4 * a) - 1) = q ^ (12 * a) * ((q ^ (4 * a) - 1) * ((q ^ (2 * a) -
        1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1))))
    (E2 : M * Nat.gcd 4 (q ^ b - 1) = q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) - 1) * (q
        ^ (4 * b) - 1)))) : False := by
  have hlt : 6 * a < 4 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_A3 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaPlus (M := 4 * b) ha hlt)

private lemma no_OmegaPlus_U4 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 6 * b)
    (E1 : M * Nat.gcd 4 (q ^ (4 * a) - 1) = q ^ (12 * a) * ((q ^ (4 * a) - 1) * ((q ^ (2 * a) -
        1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1))))
    (E2 : M * Nat.gcd 4 (q ^ b + 1) = q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) + 1) * (q
        ^ (4 * b) - 1)))) : False := by
  have hlt : 6 * a < 6 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_U4 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaPlus (M := 6 * b) ha hlt)

private lemma no_OmegaMinus_A2 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 3 * b)
    (E1 : M * Nat.gcd 4 (q ^ (4 * a) + 1) = q ^ (12 * a) * ((q ^ (4 * a) + 1) * ((q ^ (2 * a) -
        1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1))))
    (E2 : M * Nat.gcd 3 (q ^ b - 1) = q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) - 1))) :
        False := by
  have hlt : 8 * a < 3 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_A2 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaMinus (M := 3 * b) ha hlt)

private lemma no_OmegaMinus_U3 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 3 * b)
    (E1 : M * Nat.gcd 4 (q ^ (4 * a) + 1) = q ^ (12 * a) * ((q ^ (4 * a) + 1) * ((q ^ (2 * a) -
        1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1))))
    (E2 : M * Nat.gcd 3 (q ^ b + 1) = q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) + 1))) :
        False := by
  have hlt : 8 * a < 6 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_U3 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaMinus (M := 6 * b) ha hlt)

private lemma no_OmegaMinus_B2 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 4 * b)
    (E1 : M * Nat.gcd 4 (q ^ (4 * a) + 1) = q ^ (12 * a) * ((q ^ (4 * a) + 1) * ((q ^ (2 * a) -
        1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1))))
    (E2 : M * Nat.gcd 2 (q ^ b - 1) = q ^ (4 * b) * ((q ^ (2 * b) - 1) * (q ^ (4 * b) - 1))) :
        False := by
  have hlt : 8 * a < 4 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_B2 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaMinus (M := 4 * b) ha hlt)

private lemma no_OmegaMinus_U4 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 6 * b)
    (E1 : M * Nat.gcd 4 (q ^ (4 * a) + 1) = q ^ (12 * a) * ((q ^ (4 * a) + 1) * ((q ^ (2 * a) -
        1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1))))
    (E2 : M * Nat.gcd 4 (q ^ b + 1) = q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) + 1) * (q
        ^ (4 * b) - 1)))) : False := by
  have hlt : 8 * a < 6 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_U4 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_POmegaMinus (M := 6 * b) ha hlt)

private lemma no_G2_U3 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 6 * a = 3 * b)
    (E1 : M * 1 = q ^ (6 * a) * ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1)))
    (E2 : M * Nat.gcd 3 (q ^ b + 1) = q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) + 1))) :
        False := by
  have hlt : 6 * a < 6 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_U3 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_G2 (M := 6 * b) ha hlt)

private lemma no_trialityD4_U3 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 3 * b)
    (E1 : M * 1 = q ^ (12 * a) * ((q ^ (8 * a) + q ^ (4 * a) + 1) * ((q ^ (6 * a) - 1) * (q ^ (2
        * a) - 1))))
    (E2 : M * Nat.gcd 3 (q ^ b + 1) = q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) + 1))) :
        False := by
  have hlt : 12 * a < 6 * b := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_U3 hq hq2 hb (by omega)
  exact no_order_eq_of_primitive_divisor E2 E1 hr hrN hrd hq.pos (by omega)
    (goodFactor_trialityD4 (M := 6 * b) ha hlt)

private lemma no_trialityD4_A3 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 6 * b)
    (E1 : M * 1 = q ^ (12 * a) * ((q ^ (8 * a) + q ^ (4 * a) + 1) * ((q ^ (6 * a) - 1) * (q ^ (2
        * a) - 1))))
    (E2 : M * Nat.gcd 4 (q ^ b - 1) = q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) - 1) * (q
        ^ (4 * b) - 1)))) : False := by
  have hlt : 4 * b < 12 * a := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_trialityD4 hq hq2 ha (by omega) hq.pos
  exact no_order_eq_of_primitive_divisor E1 E2 hr hrN hrd hq.pos (by omega)
    (goodFactor_A3 (M := 12 * a) hb hlt)

private lemma no_G2_A3 {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 6 * a = 6 * b)
    (E1 : M * 1 = q ^ (6 * a) * ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1)))
    (E2 : M * Nat.gcd 4 (q ^ b - 1) =
      q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) - 1) * (q ^ (4 * b) - 1)))) :
    False := by
  have hlt : 4 * b < 6 * a := by omega
  obtain ⟨r, hr, hrN, hrd⟩ := exists_prim_G2 hq hq2 ha (by omega)
  exact no_order_eq_of_primitive_divisor E1 E2 hr hrN hrd hq.pos (by omega)
    (goodFactor_A3 (M := 6 * a) hb hlt)

private lemma no_G2_A2_ratio {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 6 * a = 3 * b)
    (E1 : M * 1 = q ^ (6 * a) * ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1)))
    (E2 : M * Nat.gcd 3 (q ^ b - 1) =
      q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) - 1))) : False := by
  have hba : b = 2 * a := by omega
  subst hba
  have hs3 : 3 ≤ q ^ a := by
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    calc 3 ≤ q := hq3
      _ = q ^ 1 := by ring
      _ ≤ q ^ a := Nat.pow_le_pow_right (by omega) ha
  have e : ∀ k : ℕ, q ^ (k * a) = (q ^ a) ^ k := fun k => by rw [mul_comm, pow_mul]
  have hM1 : M * 1 = (q ^ a) ^ 6 * (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1)) := by
    rw [E1, e 6, e 2]
  have hMd : M * Nat.gcd 3 ((q ^ a) ^ 2 - 1) =
      (q ^ a) ^ 6 * (((q ^ a) ^ 4 - 1) * ((q ^ a) ^ 6 - 1)) := by
    have e2 : (q ^ a) ^ 2 = q ^ (2 * a) := by rw [mul_comm, pow_mul]
    rw [e2, E2]
    rw [show 3 * (2 * a) = 6 * a by ring, show 2 * (2 * a) = 4 * a by ring, e 6, e 4]
  generalize hqs : q ^ a = s at hs3 hM1 hMd
  have key : Nat.gcd 3 (s ^ 2 - 1) *
      (s ^ 6 * ((s ^ 6 - 1) * (s ^ 2 - 1))) =
      s ^ 6 * ((s ^ 4 - 1) * (s ^ 6 - 1)) := by
    simpa using cross_mul_eq_of_mul_eq (M := M) (d1 := 1) hM1 hMd
  have hN2 : s ^ 6 * ((s ^ 4 - 1) * (s ^ 6 - 1)) =
      (s ^ 2 + 1) * (s ^ 6 * ((s ^ 6 - 1) * (s ^ 2 - 1))) := by
    have hfac4 : s ^ 4 - 1 = (s ^ 2 - 1) * (s ^ 2 + 1) := by
      simpa [show 4 = 2 * 2 by norm_num] using pow_two_mul_sub_one s 2
    rw [hfac4]; ring
  rw [hN2] at key
  have hN1 : 0 < s ^ 6 * ((s ^ 6 - 1) * (s ^ 2 - 1)) := by
    have h1 : 1 < s ^ 6 := Nat.one_lt_pow (by omega) (by omega : 1 < s)
    have h2 : 1 < s ^ 2 := Nat.one_lt_pow (by omega) (by omega : 1 < s)
    have hpos6 : 0 < s ^ 6 - 1 := by omega
    have hpos2 : 0 < s ^ 2 - 1 := by omega
    exact Nat.mul_pos (by positivity) (Nat.mul_pos hpos6 hpos2)
  have hd : Nat.gcd 3 (s ^ 2 - 1) = s ^ 2 + 1 :=
    Nat.eq_of_mul_eq_mul_right hN1 key
  have hle : Nat.gcd 3 (s ^ 2 - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  nlinarith [hd, hle, hs3]

private lemma no_OmegaMinus_A3_ratio {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 6 * b)
    (E1 : M * Nat.gcd 4 (q ^ (4 * a) + 1) =
      q ^ (12 * a) * ((q ^ (4 * a) + 1) *
        ((q ^ (2 * a) - 1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1))))
    (E2 : M * Nat.gcd 4 (q ^ b - 1) =
      q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) - 1) * (q ^ (4 * b) - 1)))) :
    False := by
  have hba : b = 2 * a := by omega
  subst hba
  have hs3 : 3 ≤ q ^ a := by
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    calc 3 ≤ q := hq3
      _ = q ^ 1 := by ring
      _ ≤ q ^ a := Nat.pow_le_pow_right (by omega) ha
  have e : ∀ k : ℕ, q ^ (k * a) = (q ^ a) ^ k := fun k => by rw [mul_comm, pow_mul]
  have hM1 : M * Nat.gcd 4 ((q ^ a) ^ 4 + 1) =
      (q ^ a) ^ 12 * (((q ^ a) ^ 4 + 1) *
        (((q ^ a) ^ 2 - 1) * ((q ^ a) ^ 4 - 1) * ((q ^ a) ^ 6 - 1))) := by
    rw [show (q ^ a) ^ 4 = q ^ (4 * a) by rw [mul_comm, pow_mul],
      show (q ^ a) ^ 12 = q ^ (12 * a) by rw [mul_comm, pow_mul],
      show (q ^ a) ^ 2 = q ^ (2 * a) by rw [mul_comm, pow_mul],
      show (q ^ a) ^ 6 = q ^ (6 * a) by rw [mul_comm, pow_mul]]
    exact E1
  have hMd : M * Nat.gcd 4 ((q ^ a) ^ 2 - 1) =
      (q ^ a) ^ 12 * (((q ^ a) ^ 4 - 1) *
        (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 8 - 1))) := by
    have e2 : (q ^ a) ^ 2 = q ^ (2 * a) := by rw [mul_comm, pow_mul]
    rw [e2, E2]
    rw [show 6 * (2 * a) = 12 * a by ring, show 2 * (2 * a) = 4 * a by ring,
      show 3 * (2 * a) = 6 * a by ring, show 4 * (2 * a) = 8 * a by ring,
      e 12, e 4, e 6, e 8]
  generalize hqs : q ^ a = s at hs3 hM1 hMd
  have key : Nat.gcd 4 (s ^ 2 - 1) *
      (s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * (s ^ 4 - 1) * (s ^ 6 - 1)))) =
      Nat.gcd 4 (s ^ 4 + 1) * (s ^ 12 * ((s ^ 4 - 1) * ((s ^ 6 - 1) * (s ^ 8 - 1)))) :=
    cross_mul_eq_of_mul_eq (M := M) hM1 hMd
  have hN2 : s ^ 12 * ((s ^ 4 - 1) * ((s ^ 6 - 1) * (s ^ 8 - 1))) =
      (s ^ 2 + 1) * (s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * (s ^ 4 - 1) * (s ^ 6 - 1)))) := by
    have hfac8 : s ^ 8 - 1 = (s ^ 4 - 1) * (s ^ 4 + 1) := by
      simpa [show 8 = 2 * 4 by norm_num] using pow_two_mul_sub_one s 4
    have hfac4 : s ^ 4 - 1 = (s ^ 2 - 1) * (s ^ 2 + 1) := by
      simpa [show 4 = 2 * 2 by norm_num] using pow_two_mul_sub_one s 2
    rw [hfac8, hfac4]; ring
  rw [hN2] at key
  have hN1 : 0 < s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * (s ^ 4 - 1) * (s ^ 6 - 1))) := by
    have h2 : 1 < s ^ 2 := Nat.one_lt_pow (by omega) (by omega : 1 < s)
    have h4 : 1 < s ^ 4 := Nat.one_lt_pow (by omega) (by omega : 1 < s)
    have h6 : 1 < s ^ 6 := Nat.one_lt_pow (by omega) (by omega : 1 < s)
    have p2 : 0 < s ^ 2 - 1 := by omega
    have p4 : 0 < s ^ 4 - 1 := by omega
    have p6 : 0 < s ^ 6 - 1 := by omega
    exact Nat.mul_pos (by positivity) (Nat.mul_pos (by positivity)
      (Nat.mul_pos (Nat.mul_pos p2 p4) p6))
  have key' : Nat.gcd 4 (s ^ 2 - 1) *
      (s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * (s ^ 4 - 1) * (s ^ 6 - 1)))) =
      (Nat.gcd 4 (s ^ 4 + 1) * (s ^ 2 + 1)) *
        (s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * (s ^ 4 - 1) * (s ^ 6 - 1)))) := by
    calc Nat.gcd 4 (s ^ 2 - 1) *
        (s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * (s ^ 4 - 1) * (s ^ 6 - 1))))
        = Nat.gcd 4 (s ^ 4 + 1) * ((s ^ 2 + 1) *
            (s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * (s ^ 4 - 1) * (s ^ 6 - 1))))) := key
      _ = (Nat.gcd 4 (s ^ 4 + 1) * (s ^ 2 + 1)) *
            (s ^ 12 * ((s ^ 4 + 1) * ((s ^ 2 - 1) * (s ^ 4 - 1) * (s ^ 6 - 1)))) := by ring
  have hd : Nat.gcd 4 (s ^ 2 - 1) = Nat.gcd 4 (s ^ 4 + 1) * (s ^ 2 + 1) :=
    Nat.eq_of_mul_eq_mul_right hN1 key'
  have hle : Nat.gcd 4 (s ^ 2 - 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  have hge : 1 ≤ Nat.gcd 4 (s ^ 4 + 1) := Nat.gcd_pos_of_pos_right _ (by positivity)
  have h2 : 10 ≤ s ^ 2 + 1 := by nlinarith
  nlinarith [hd, hle, hge, h2]
private lemma no_L2_U3_ratio {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 1 * a = 3 * b)
    (E1 : M * 2 = q ^ a * (q ^ (2 * a) - 1))
    (E2 : M * Nat.gcd 3 (q ^ b + 1) =
      q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) + 1))) : False := by
  have hab : a = 3 * b := by omega
  subst hab
  have hs3 : 3 ≤ q ^ b := by
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    calc 3 ≤ q := hq3
      _ = q ^ 1 := by ring
      _ ≤ q ^ b := Nat.pow_le_pow_right (by omega) hb
  have e : ∀ k : ℕ, q ^ (k * b) = (q ^ b) ^ k := fun k => by rw [mul_comm, pow_mul]
  have hM2 : M * 2 = (q ^ b) ^ 3 * ((q ^ b) ^ 6 - 1) := by
    rw [E1]
    rw [show 3 * b = 3 * b by rfl, show 2 * (3 * b) = 6 * b by ring, e 3, e 6]
  have hMd : M * Nat.gcd 3 (q ^ b + 1) =
      (q ^ b) ^ 3 * (((q ^ b) ^ 2 - 1) * ((q ^ b) ^ 3 + 1)) := by
    rw [E2, e 3, e 2]
  generalize hqs : q ^ b = s at hs3 hM2 hMd
  have key : Nat.gcd 3 (s + 1) * (s ^ 3 * ((s ^ 6 - 1))) =
      2 * (s ^ 3 * ((s ^ 2 - 1) * (s ^ 3 + 1))) := by
    exact cross_mul_eq_of_mul_eq (M := M) hM2 hMd
  have hfac6 : s ^ 6 - 1 = (s ^ 3 - 1) * (s ^ 3 + 1) := by
    simpa [show 6 = 2 * 3 by norm_num] using pow_two_mul_sub_one s 3
  rw [hfac6] at key
  have hC : 0 < s ^ 3 * (s ^ 3 + 1) := by positivity
  have key' : Nat.gcd 3 (s + 1) * (s ^ 3 * ((s ^ 3 - 1) * (s ^ 3 + 1))) =
      2 * (s ^ 3 * ((s ^ 2 - 1) * (s ^ 3 + 1))) := key
  have hN1 : s ^ 3 * ((s ^ 3 - 1) * (s ^ 3 + 1)) =
      (s ^ 3 * (s ^ 3 + 1)) * (s ^ 3 - 1) := by ring
  have hN2 : s ^ 3 * ((s ^ 2 - 1) * (s ^ 3 + 1)) =
      (s ^ 3 * (s ^ 3 + 1)) * (s ^ 2 - 1) := by ring
  rw [hN1, hN2] at key'
  have key'' : Nat.gcd 3 (s + 1) * (s ^ 3 - 1) = 2 * (s ^ 2 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hC
    simpa [mul_assoc, mul_comm, mul_left_comm] using key'
  have hd1 : 1 ≤ Nat.gcd 3 (s + 1) := Nat.gcd_pos_of_pos_right _ (by omega)
  have hbig : 2 * (s ^ 2 - 1) < s ^ 3 - 1 := by
    have h : 2 * s ^ 2 ≤ s ^ 3 := by
      calc 2 * s ^ 2 ≤ s ^ 2 * s := by nlinarith [hs3]
        _ = s ^ 3 := by ring
    have h2 : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have hge : s ^ 3 - 1 ≤ Nat.gcd 3 (s + 1) * (s ^ 3 - 1) := by
    calc s ^ 3 - 1 = 1 * (s ^ 3 - 1) := by ring
      _ ≤ Nat.gcd 3 (s + 1) * (s ^ 3 - 1) := Nat.mul_le_mul_right _ hd1
  rw [key''] at hge
  exact (not_le.mpr hbig) hge
private lemma no_G2_B2_ratio {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 6 * a = 4 * b)
    (E1 : M * 1 = q ^ (6 * a) * ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1)))
    (E2 : M * Nat.gcd 2 (q ^ b - 1) =
      q ^ (4 * b) * ((q ^ (2 * b) - 1) * (q ^ (4 * b) - 1))) : False := by
  obtain ⟨c, rfl, rfl⟩ : ∃ c, a = 2 * c ∧ b = 3 * c := ⟨a / 2, by omega, by omega⟩
  have hc : 0 < c := by omega
  have hs3 : 3 ≤ q ^ c := by
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    calc 3 ≤ q := hq3
      _ = q ^ 1 := by ring
      _ ≤ q ^ c := Nat.pow_le_pow_right (by omega) hc
  have e : ∀ k : ℕ, q ^ (k * c) = (q ^ c) ^ k := fun k => by rw [mul_comm, pow_mul]
  have hM1 : M * 1 = (q ^ c) ^ 12 * (((q ^ c) ^ 12 - 1) * ((q ^ c) ^ 4 - 1)) := by
    rw [E1]
    rw [show 6 * (2 * c) = 12 * c by ring, show 2 * (2 * c) = 4 * c by ring, e 12, e 4]
  have hMd : M * Nat.gcd 2 ((q ^ c) ^ 3 - 1) =
      (q ^ c) ^ 12 * (((q ^ c) ^ 6 - 1) * ((q ^ c) ^ 12 - 1)) := by
    have e3 : (q ^ c) ^ 3 = q ^ (3 * c) := by rw [mul_comm, pow_mul]
    rw [e3, E2]
    rw [show 4 * (3 * c) = 12 * c by ring, show 2 * (3 * c) = 6 * c by ring, e 12, e 6]
  generalize hqs : q ^ c = s at hs3 hM1 hMd
  have key : Nat.gcd 2 (s ^ 3 - 1) *
      (s ^ 12 * ((s ^ 12 - 1) * (s ^ 4 - 1))) =
      1 * (s ^ 12 * ((s ^ 6 - 1) * (s ^ 12 - 1))) :=
    cross_mul_eq_of_mul_eq (M := M) hM1 hMd
  have hC : 0 < s ^ 12 * (s ^ 12 - 1) := by
    have h1 : 1 < s ^ 12 := Nat.one_lt_pow (by omega) (by omega : 1 < s)
    have h2 : 0 < s ^ 12 - 1 := by omega
    positivity
  have hN1 : s ^ 12 * ((s ^ 12 - 1) * (s ^ 4 - 1)) =
      (s ^ 12 * (s ^ 12 - 1)) * (s ^ 4 - 1) := by ring
  have hN2 : s ^ 12 * ((s ^ 6 - 1) * (s ^ 12 - 1)) =
      (s ^ 12 * (s ^ 12 - 1)) * (s ^ 6 - 1) := by ring
  rw [hN1, hN2] at key
  have key' : Nat.gcd 2 (s ^ 3 - 1) * (s ^ 4 - 1) = 1 * (s ^ 6 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hC
    simpa [mul_assoc, mul_comm, mul_left_comm] using key
  rw [one_mul] at key'
  have hd2 : Nat.gcd 2 (s ^ 3 - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  have hbig : 2 * (s ^ 4 - 1) < s ^ 6 - 1 := by
    have hs2 : 2 < s ^ 2 := by nlinarith
    have h : 2 * s ^ 4 < s ^ 6 := by
      calc 2 * s ^ 4 = s ^ 4 * 2 := by ring
        _ < s ^ 4 * s ^ 2 := Nat.mul_lt_mul_of_pos_left hs2 (by positivity)
        _ = s ^ 6 := by ring
    have h4 : 1 ≤ s ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h6 : 1 ≤ s ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  have hle : Nat.gcd 2 (s ^ 3 - 1) * (s ^ 4 - 1) ≤ 2 * (s ^ 4 - 1) :=
    Nat.mul_le_mul_right _ hd2
  rw [key'] at hle
  exact (not_le.mpr hbig) hle
private lemma no_trialityD4_B2_ratio {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 4 * b)
    (E1 : M * 1 = q ^ (12 * a) * ((q ^ (8 * a) + q ^ (4 * a) + 1) *
      ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1))))
    (E2 : M * Nat.gcd 2 (q ^ b - 1) =
      q ^ (4 * b) * ((q ^ (2 * b) - 1) * (q ^ (4 * b) - 1))) : False := by
  have hba : b = 3 * a := by omega
  subst hba
  have hs3 : 3 ≤ q ^ a := by
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    calc 3 ≤ q := hq3
      _ = q ^ 1 := by ring
      _ ≤ q ^ a := Nat.pow_le_pow_right (by omega) ha
  have e : ∀ k : ℕ, q ^ (k * a) = (q ^ a) ^ k := fun k => by rw [mul_comm, pow_mul]
  have hM1 : M * 1 = (q ^ a) ^ 12 * (((q ^ a) ^ 8 + (q ^ a) ^ 4 + 1) *
      (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1))) := by
    rw [E1, e 12, e 8, e 4, e 6, e 2]
  have hMd : M * Nat.gcd 2 ((q ^ a) ^ 3 - 1) =
      (q ^ a) ^ 12 * (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 12 - 1)) := by
    have e3 : (q ^ a) ^ 3 = q ^ (3 * a) := by rw [mul_comm, pow_mul]
    rw [e3, E2]
    rw [show 4 * (3 * a) = 12 * a by ring, show 2 * (3 * a) = 6 * a by ring, e 12, e 6]
  generalize hqs : q ^ a = s at hs3 hM1 hMd
  have key : Nat.gcd 2 (s ^ 3 - 1) *
      (s ^ 12 * ((s ^ 8 + s ^ 4 + 1) * ((s ^ 6 - 1) * (s ^ 2 - 1)))) =
      1 * (s ^ 12 * ((s ^ 6 - 1) * (s ^ 12 - 1))) :=
    cross_mul_eq_of_mul_eq (M := M) hM1 hMd
  have hN2 : s ^ 12 * ((s ^ 6 - 1) * (s ^ 12 - 1)) =
      (s ^ 2 + 1) * (s ^ 12 * ((s ^ 8 + s ^ 4 + 1) * ((s ^ 6 - 1) * (s ^ 2 - 1)))) := by
    have hfac12 : s ^ 12 - 1 = (s ^ 4 - 1) * (s ^ 8 + s ^ 4 + 1) := by
      simpa [show 3 * 4 = 12 by norm_num, show 2 * 4 = 8 by norm_num]
        using pow_three_mul_sub_one (by positivity : 0 < s) (m := 4)
    have hfac4 : s ^ 4 - 1 = (s ^ 2 - 1) * (s ^ 2 + 1) := by
      simpa [show 4 = 2 * 2 by norm_num] using pow_two_mul_sub_one s 2
    rw [hfac12, hfac4]; ring
  rw [hN2] at key
  rw [one_mul] at key
  have hN1 : 0 < s ^ 12 * ((s ^ 8 + s ^ 4 + 1) * ((s ^ 6 - 1) * (s ^ 2 - 1))) := by
    have h6 : 1 < s ^ 6 := Nat.one_lt_pow (by omega) (by omega : 1 < s)
    have h2 : 1 < s ^ 2 := Nat.one_lt_pow (by omega) (by omega : 1 < s)
    have p6 : 0 < s ^ 6 - 1 := by omega
    have p2 : 0 < s ^ 2 - 1 := by omega
    exact Nat.mul_pos (by positivity) (Nat.mul_pos (by positivity) (Nat.mul_pos p6 p2))
  have hd : Nat.gcd 2 (s ^ 3 - 1) = s ^ 2 + 1 := by
    have key' : Nat.gcd 2 (s ^ 3 - 1) *
        (s ^ 12 * ((s ^ 8 + s ^ 4 + 1) * ((s ^ 6 - 1) * (s ^ 2 - 1)))) =
        (s ^ 2 + 1) * (s ^ 12 * ((s ^ 8 + s ^ 4 + 1) * ((s ^ 6 - 1) * (s ^ 2 - 1)))) := by
      rw [← key]
    exact Nat.eq_of_mul_eq_mul_right hN1 key'
  have hle : Nat.gcd 2 (s ^ 3 - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  nlinarith [hd, hle, hs3]
private lemma no_OmegaOdd_A3_secondary {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 9 * a = 6 * b)
    (E1 : M * 2 = q ^ (9 * a) *
      ((q ^ (2 * a) - 1) * (q ^ (4 * a) - 1) * (q ^ (6 * a) - 1)))
    (E2 : M * Nat.gcd 4 (q ^ b - 1) =
      q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) - 1) * (q ^ (4 * b) - 1)))) :
    False := by
  obtain ⟨c, rfl, rfl⟩ : ∃ c, a = 2 * c ∧ b = 3 * c := ⟨a / 2, by omega, by omega⟩
  have hc : 0 < c := by omega
  have e : ∀ k : ℕ, q ^ (k * c) = (q ^ c) ^ k := fun k => by rw [mul_comm, pow_mul]
  have hM2 : M * 2 = (q ^ c) ^ 18 *
      (((q ^ c) ^ 4 - 1) * ((q ^ c) ^ 8 - 1) * ((q ^ c) ^ 12 - 1)) := by
    rw [E1]
    rw [show 9 * (2 * c) = 18 * c by ring, show 2 * (2 * c) = 4 * c by ring,
      show 4 * (2 * c) = 8 * c by ring, show 6 * (2 * c) = 12 * c by ring,
      e 18, e 4, e 8, e 12]
  have hMd : M * Nat.gcd 4 ((q ^ c) ^ 3 - 1) =
      (q ^ c) ^ 18 * (((q ^ c) ^ 6 - 1) * (((q ^ c) ^ 9 - 1) * ((q ^ c) ^ 12 - 1))) := by
    have e3 : (q ^ c) ^ 3 = q ^ (3 * c) := by rw [mul_comm, pow_mul]
    rw [e3, E2]
    rw [show 6 * (3 * c) = 18 * c by ring, show 2 * (3 * c) = 6 * c by ring,
      show 3 * (3 * c) = 9 * c by ring, show 4 * (3 * c) = 12 * c by ring,
      e 18, e 6, e 9, e 12]
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) (show 3 ≤ 8 * c by
      omega)
  have hr2 : r ≠ 2 := hr.ne_two (hq.odd_of_ne_two hq2) (by omega)
  have h8 : r ∣ (q ^ c) ^ 8 - 1 := by rw [← e 8]; exact hr.2.1
  have hrN1 : r ∣ (q ^ c) ^ 18 *
      (((q ^ c) ^ 4 - 1) * ((q ^ c) ^ 8 - 1) * ((q ^ c) ^ 12 - 1)) :=
    dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h8 ((q ^ c) ^ 4 - 1))
        ((q ^ c) ^ 12 - 1)) ((q ^ c) ^ 18)
  have hrM : r ∣ M := by
    have h : r ∣ M * 2 := by rw [hM2]; exact hrN1
    exact (hr.1.dvd_mul.mp h).resolve_right (hr.not_dvd_small hq.pos (by omega : 4 ≤ 8 * c) (by
        norm_num) (by norm_num))
  have h6 : ¬ r ∣ (q ^ c) ^ 6 - 1 := by
    intro hd
    have hd' : r ∣ q ^ (6 * c) - 1 := by rw [e 6]; exact hd
    exact ((mul_dvd_mul_iff_right hc.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 6))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * c) (6 * c)).mp hd')
  have h9 : ¬ r ∣ (q ^ c) ^ 9 - 1 := by
    intro hd
    have hd' : r ∣ q ^ (9 * c) - 1 := by rw [e 9]; exact hd
    exact ((mul_dvd_mul_iff_right hc.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 9))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * c) (9 * c)).mp hd')
  have h12 : ¬ r ∣ (q ^ c) ^ 12 - 1 := by
    intro hd
    have hd' : r ∣ q ^ (12 * c) - 1 := by rw [e 12]; exact hd
    exact ((mul_dvd_mul_iff_right hc.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 12))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * c) (12 * c)).mp hd')
  have hnot : ¬ r ∣ (q ^ c) ^ 18 *
      (((q ^ c) ^ 6 - 1) * (((q ^ c) ^ 9 - 1) * ((q ^ c) ^ 12 - 1))) := by
    intro hd
    have hrq : ¬ r ∣ (q ^ c) ^ 18 := by
      intro h
      have h' : r ∣ q ^ (18 * c) := by rw [e 18]; exact h
      exact hr.not_dvd_base hq.pos (by omega) (hr.1.dvd_of_dvd_pow h')
    rcases hr.1.dvd_mul.mp hd with h | h
    · exact hrq h
    · rcases hr.1.dvd_mul.mp h with h | h
      · exact h6 h
      · rcases hr.1.dvd_mul.mp h with h | h
        · exact h9 h
        · exact h12 h
  have : r ∣ (q ^ c) ^ 18 *
      (((q ^ c) ^ 6 - 1) * (((q ^ c) ^ 9 - 1) * ((q ^ c) ^ 12 - 1))) := by
    rw [← hMd]
    exact dvd_mul_of_dvd_left hrM _
  exact hnot this
private lemma no_G2_U4_secondary {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 6 * a = 6 * b)
    (E1 : M * 1 = q ^ (6 * a) * ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1)))
    (E2 : M * Nat.gcd 4 (q ^ b + 1) =
      q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) + 1) * (q ^ (4 * b) - 1)))) :
    False := by
  have hab : a = b := by omega
  subst hab
  have e : ∀ k : ℕ, q ^ (k * a) = (q ^ a) ^ k := fun k => by rw [mul_comm, pow_mul]
  have hM1 : M * 1 = (q ^ a) ^ 6 * (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1)) := by
    rw [E1, e 6, e 2]
  have hMd : M * Nat.gcd 4 (q ^ a + 1) =
      (q ^ a) ^ 6 * (((q ^ a) ^ 2 - 1) * (((q ^ a) ^ 3 + 1) * ((q ^ a) ^ 4 - 1))) := by
    rw [show (q ^ a) ^ 6 = q ^ (6 * a) by rw [mul_comm, pow_mul],
      show (q ^ a) ^ 2 = q ^ (2 * a) by rw [mul_comm, pow_mul],
      show (q ^ a) ^ 3 = q ^ (3 * a) by rw [mul_comm, pow_mul],
      show (q ^ a) ^ 4 = q ^ (4 * a) by rw [mul_comm, pow_mul]]
    exact E2
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) (show 3 ≤ 4 * a by
      omega)
  have h4 : r ∣ (q ^ a) ^ 4 - 1 := by rw [← e 4]; exact hr.2.1
  have hrN2 : r ∣ (q ^ a) ^ 6 * (((q ^ a) ^ 2 - 1) * (((q ^ a) ^ 3 + 1) * ((q ^ a) ^ 4 - 1))) :=
    dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_right h4 (((q ^ a) ^ 3 + 1))) ((q ^ a) ^ 2 - 1)) _
  have hrd : ¬ r ∣ Nat.gcd 4 ((q ^ a) + 1) := by
    intro hd
    have h1 : r ∣ (q ^ a) + 1 := hd.trans (Nat.gcd_dvd_right 4 _)
    have h2 : r ∣ (q ^ a) ^ 2 - 1 := by
      have e2 : (q ^ a) ^ 2 - 1 = ((q ^ a) - 1) * ((q ^ a) + 1) := by
        simpa using pow_two_mul_sub_one (q ^ a) 1
      rw [e2]; exact dvd_mul_of_dvd_right h1 _
    have h3 : r ∣ q ^ (2 * a) - 1 := by rw [e 2]; exact h2
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (4 : ℕ) ∣ 2))
      ((hr.dvd_iff hq.pos (by omega : 0 < 4 * a) (2 * a)).mp h3)
  have hrM : r ∣ M := by
    have h : r ∣ M * Nat.gcd 4 ((q ^ a) + 1) := by rw [hMd]; exact hrN2
    exact (hr.1.dvd_mul.mp h).resolve_right hrd
  have h6 : ¬ r ∣ (q ^ a) ^ 6 - 1 := by
    intro hd
    have hd' : r ∣ q ^ (6 * a) - 1 := by rw [e 6]; exact hd
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (4 : ℕ) ∣ 6))
      ((hr.dvd_iff hq.pos (by omega : 0 < 4 * a) (6 * a)).mp hd')
  have h2 : ¬ r ∣ (q ^ a) ^ 2 - 1 := by
    intro hd
    have hd' : r ∣ q ^ (2 * a) - 1 := by rw [e 2]; exact hd
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (4 : ℕ) ∣ 2))
      ((hr.dvd_iff hq.pos (by omega : 0 < 4 * a) (2 * a)).mp hd')
  have hnot : ¬ r ∣ (q ^ a) ^ 6 * (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1)) := by
    intro hd
    have hrq : ¬ r ∣ (q ^ a) ^ 6 := by
      intro h
      have h' : r ∣ q ^ (6 * a) := by rw [e 6]; exact h
      exact hr.not_dvd_base hq.pos (by omega) (hr.1.dvd_of_dvd_pow h')
    rcases hr.1.dvd_mul.mp hd with h | h
    · exact hrq h
    · rcases hr.1.dvd_mul.mp h with h | h
      · exact h6 h
      · exact h2 h
  have : r ∣ (q ^ a) ^ 6 * (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1)) := by
    rw [← hM1]; exact dvd_mul_of_dvd_left hrM _
  exact hnot this

private lemma no_trialityD4_A2_secondary {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 3 * b)
    (E1 : M * 1 = q ^ (12 * a) * ((q ^ (8 * a) + q ^ (4 * a) + 1) *
      ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1))))
    (E2 : M * Nat.gcd 3 (q ^ b - 1) =
      q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) - 1))) : False := by
  have hba : b = 4 * a := by omega
  subst hba
  have e : ∀ k : ℕ, q ^ (k * a) = (q ^ a) ^ k := fun k => by rw [mul_comm, pow_mul]
  have hM1 : M * 1 = (q ^ a) ^ 12 * (((q ^ a) ^ 8 + (q ^ a) ^ 4 + 1) *
      (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1))) := by
    rw [E1, e 12, e 8, e 4, e 6, e 2]
  have hMd : M * Nat.gcd 3 ((q ^ a) ^ 4 - 1) =
      (q ^ a) ^ 12 * (((q ^ a) ^ 8 - 1) * ((q ^ a) ^ 12 - 1)) := by
    have e4 : (q ^ a) ^ 4 = q ^ (4 * a) := by rw [mul_comm, pow_mul]
    rw [e4, E2]
    rw [show 3 * (4 * a) = 12 * a by ring, show 2 * (4 * a) = 8 * a by ring, e 12, e 8]
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) (show 3 ≤ 8 * a by
      omega)
  have h8 : r ∣ (q ^ a) ^ 8 - 1 := by rw [← e 8]; exact hr.2.1
  have hrN : r ∣ (q ^ a) ^ 12 * (((q ^ a) ^ 8 - 1) * ((q ^ a) ^ 12 - 1)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h8 ((q ^ a) ^ 12 - 1)) ((q ^ a) ^ 12)
  have hrd : ¬ r ∣ Nat.gcd 3 ((q ^ a) ^ 4 - 1) := by
    intro hd
    have h1 : r ∣ (q ^ a) ^ 4 - 1 := hd.trans (Nat.gcd_dvd_right 3 _)
    have h1' : r ∣ q ^ (4 * a) - 1 := by rw [e 4]; exact h1
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 4))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * a) (4 * a)).mp h1')
  have hrM : r ∣ M := by
    have h : r ∣ M * Nat.gcd 3 ((q ^ a) ^ 4 - 1) := by rw [hMd]; exact hrN
    exact (hr.1.dvd_mul.mp h).resolve_right hrd
  have h6 : ¬ r ∣ (q ^ a) ^ 6 - 1 := by
    intro hd
    have hd' : r ∣ q ^ (6 * a) - 1 := by rw [e 6]; exact hd
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 6))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * a) (6 * a)).mp hd')
  have h2 : ¬ r ∣ (q ^ a) ^ 2 - 1 := by
    intro hd
    have hd' : r ∣ q ^ (2 * a) - 1 := by rw [e 2]; exact hd
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 2))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * a) (2 * a)).mp hd')
  have hT : ¬ r ∣ (q ^ a) ^ 8 + (q ^ a) ^ 4 + 1 := by
    intro hd
    have hfac : (q ^ a) ^ 12 - 1 = ((q ^ a) ^ 4 - 1) * ((q ^ a) ^ 8 + (q ^ a) ^ 4 + 1) := by
      simpa [show 12 = 3 * 4 by norm_num, show 8 = 2 * 4 by norm_num]
        using pow_three_mul_sub_one (q := q ^ a) (pow_pos hq.pos a) (m := 4)
    have h12 : r ∣ (q ^ a) ^ 12 - 1 := by
      rw [hfac]; exact dvd_mul_of_dvd_right hd _
    have h12' : r ∣ q ^ (12 * a) - 1 := by rw [e 12]; exact h12
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 12))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * a) (12 * a)).mp h12')
  have hnot : ¬ r ∣ (q ^ a) ^ 12 * (((q ^ a) ^ 8 + (q ^ a) ^ 4 + 1) *
      (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1))) := by
    intro hd
    have hrq : ¬ r ∣ (q ^ a) ^ 12 := by
      intro h
      have h' : r ∣ q ^ (12 * a) := by rw [e 12]; exact h
      exact hr.not_dvd_base hq.pos (by omega) (hr.1.dvd_of_dvd_pow h')
    rcases hr.1.dvd_mul.mp hd with h | h
    · exact hrq h
    · rcases hr.1.dvd_mul.mp h with h | h
      · exact hT h
      · rcases hr.1.dvd_mul.mp h with h | h
        · exact h6 h
        · exact h2 h
  have : r ∣ (q ^ a) ^ 12 * (((q ^ a) ^ 8 + (q ^ a) ^ 4 + 1) *
      (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1))) := by
    rw [← hM1]; exact dvd_mul_of_dvd_left hrM _
  exact hnot this

private lemma no_trialityD4_U4_secondary {M q a b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hrel : 12 * a = 6 * b)
    (E1 : M * 1 = q ^ (12 * a) * ((q ^ (8 * a) + q ^ (4 * a) + 1) *
      ((q ^ (6 * a) - 1) * (q ^ (2 * a) - 1))))
    (E2 : M * Nat.gcd 4 (q ^ b + 1) =
      q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) + 1) * (q ^ (4 * b) - 1)))) :
    False := by
  have hba : b = 2 * a := by omega
  subst hba
  have e : ∀ k : ℕ, q ^ (k * a) = (q ^ a) ^ k := fun k => by rw [mul_comm, pow_mul]
  have hM1 : M * 1 = (q ^ a) ^ 12 * (((q ^ a) ^ 8 + (q ^ a) ^ 4 + 1) *
      (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1))) := by
    rw [E1, e 12, e 8, e 4, e 6, e 2]
  have hMd : M * Nat.gcd 4 ((q ^ a) ^ 2 + 1) =
      (q ^ a) ^ 12 * (((q ^ a) ^ 4 - 1) * (((q ^ a) ^ 6 + 1) * ((q ^ a) ^ 8 - 1))) := by
    have e2 : (q ^ a) ^ 2 = q ^ (2 * a) := by rw [mul_comm, pow_mul]
    rw [e2, E2]
    rw [show 6 * (2 * a) = 12 * a by ring, show 2 * (2 * a) = 4 * a by ring,
      show 3 * (2 * a) = 6 * a by ring, show 4 * (2 * a) = 8 * a by ring,
      e 12, e 4, e 6, e 8]
  obtain ⟨r, hr⟩ := exists_isPrimDiv (a := q) (by have := hq.two_le; omega) (show 3 ≤ 8 * a by
      omega)
  have h8 : r ∣ (q ^ a) ^ 8 - 1 := by rw [← e 8]; exact hr.2.1
  have hrN : r ∣ (q ^ a) ^ 12 * (((q ^ a) ^ 4 - 1) * (((q ^ a) ^ 6 + 1) * ((q ^ a) ^ 8 - 1))) :=
    dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h8 ((q ^ a) ^ 6 + 1)) ((q ^ a) ^ 4 - 1))
      ((q ^ a) ^ 12)
  have hrd : ¬ r ∣ Nat.gcd 4 ((q ^ a) ^ 2 + 1) := by
    intro hd
    have h1 : r ∣ (q ^ a) ^ 2 + 1 := hd.trans (Nat.gcd_dvd_right 4 _)
    have h2 : r ∣ (q ^ a) ^ 4 - 1 := by
      have e4 : (q ^ a) ^ 4 - 1 = ((q ^ a) ^ 2 - 1) * ((q ^ a) ^ 2 + 1) := by
        simpa using pow_two_mul_sub_one (q ^ a) 2
      rw [e4]; exact dvd_mul_of_dvd_right h1 _
    have h2' : r ∣ q ^ (4 * a) - 1 := by
      have e4' : (q ^ a) ^ 4 = q ^ (4 * a) := by rw [mul_comm, pow_mul]
      rwa [e4'] at h2
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 4))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * a) (4 * a)).mp h2')
  have hrM : r ∣ M := by
    have h : r ∣ M * Nat.gcd 4 ((q ^ a) ^ 2 + 1) := by rw [hMd]; exact hrN
    exact (hr.1.dvd_mul.mp h).resolve_right hrd
  have h6 : ¬ r ∣ (q ^ a) ^ 6 - 1 := by
    intro hd
    have hd' : r ∣ q ^ (6 * a) - 1 := by rw [e 6]; exact hd
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 6))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * a) (6 * a)).mp hd')
  have h2 : ¬ r ∣ (q ^ a) ^ 2 - 1 := by
    intro hd
    have hd' : r ∣ q ^ (2 * a) - 1 := by rw [e 2]; exact hd
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 2))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * a) (2 * a)).mp hd')
  have hT : ¬ r ∣ (q ^ a) ^ 8 + (q ^ a) ^ 4 + 1 := by
    intro hd
    have hfac : (q ^ a) ^ 12 - 1 = ((q ^ a) ^ 4 - 1) * ((q ^ a) ^ 8 + (q ^ a) ^ 4 + 1) := by
      simpa [show 12 = 3 * 4 by norm_num, show 8 = 2 * 4 by norm_num]
        using pow_three_mul_sub_one (q := q ^ a) (pow_pos hq.pos a) (m := 4)
    have h12 : r ∣ (q ^ a) ^ 12 - 1 := by
      rw [hfac]; exact dvd_mul_of_dvd_right hd _
    have h12' : r ∣ q ^ (12 * a) - 1 := by rw [e 12]; exact h12
    exact ((mul_dvd_mul_iff_right ha.ne').not.mpr (by norm_num : ¬ (8 : ℕ) ∣ 12))
      ((hr.dvd_iff hq.pos (by omega : 0 < 8 * a) (12 * a)).mp h12')
  have hnot : ¬ r ∣ (q ^ a) ^ 12 * (((q ^ a) ^ 8 + (q ^ a) ^ 4 + 1) *
      (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1))) := by
    intro hd
    have hrq : ¬ r ∣ (q ^ a) ^ 12 := by
      intro h
      have h' : r ∣ q ^ (12 * a) := by rw [e 12]; exact h
      exact hr.not_dvd_base hq.pos (by omega) (hr.1.dvd_of_dvd_pow h')
    rcases hr.1.dvd_mul.mp hd with h | h
    · exact hrq h
    · rcases hr.1.dvd_mul.mp h with h | h
      · exact hT h
      · rcases hr.1.dvd_mul.mp h with h | h
        · exact h6 h
        · exact h2 h
  have : r ∣ (q ^ a) ^ 12 * (((q ^ a) ^ 8 + (q ^ a) ^ 4 + 1) *
      (((q ^ a) ^ 6 - 1) * ((q ^ a) ^ 2 - 1))) := by
    rw [← hM1]; exact dvd_mul_of_dvd_left hrM _
  exact hnot this

private def JTypeOf (S : Type) [Group S] (q : ℕ) : Prop :=
  (∃ Q : TauCeti.PrimePower, Q.p = q ∧
    (catalogIs S (onLie fun d => d = .A 2 Q) ∨
      catalogIs S (onLie fun d => d = .twistedA 2 Q))) ∨
  (∃ Q : TauCeti.PrimePower, Q.p = q ∧
    (catalogIs S (onLie fun d => d = .B 2 Q) ∨
      catalogIs S (onLie fun d => d = .A 3 Q) ∨
        catalogIs S (onLie fun d => d = .twistedA 3 Q)))

private lemma jTypeOf_of_jType {G : Type} [Group G] [Finite G] {p q : ℕ} {J : Subgroup G}
    (h : JType p q J) : JTypeOf (PSimple p J) q := by
  rcases h with ⟨Q, hQ, hA, -⟩ | ⟨Q, hQ, hB⟩
  · exact Or.inl ⟨Q, hQ, hA⟩
  · exact Or.inr ⟨Q, hQ, hB⟩

private lemma norm_A2 {M q b : ℕ}
    (h : M * Nat.gcd 3 (q ^ b - 1) = (q ^ b) ^ 3 * (((q ^ b) ^ 2 - 1) * ((q ^ b) ^ 3 - 1))) :
    M * Nat.gcd 3 (q ^ b - 1) =
      q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) - 1)) := by
  rwa [show (q ^ b) ^ 3 = q ^ (3 * b) by rw [mul_comm, pow_mul],
    show (q ^ b) ^ 2 = q ^ (2 * b) by rw [mul_comm, pow_mul]] at h

private lemma norm_U3 {M q b : ℕ}
    (h : M * Nat.gcd 3 (q ^ b + 1) = (q ^ b) ^ 3 * (((q ^ b) ^ 2 - 1) * ((q ^ b) ^ 3 + 1))) :
    M * Nat.gcd 3 (q ^ b + 1) =
      q ^ (3 * b) * ((q ^ (2 * b) - 1) * (q ^ (3 * b) + 1)) := by
  rwa [show (q ^ b) ^ 3 = q ^ (3 * b) by rw [mul_comm, pow_mul],
    show (q ^ b) ^ 2 = q ^ (2 * b) by rw [mul_comm, pow_mul]] at h

private lemma norm_B2 {M q b : ℕ}
    (h : M * Nat.gcd 2 (q ^ b - 1) = (q ^ b) ^ 4 * (((q ^ b) ^ 2 - 1) * ((q ^ b) ^ 4 - 1))) :
    M * Nat.gcd 2 (q ^ b - 1) =
      q ^ (4 * b) * ((q ^ (2 * b) - 1) * (q ^ (4 * b) - 1)) := by
  rwa [show (q ^ b) ^ 4 = q ^ (4 * b) by rw [mul_comm, pow_mul],
    show (q ^ b) ^ 2 = q ^ (2 * b) by rw [mul_comm, pow_mul]] at h

private lemma norm_A3 {M q b : ℕ}
    (h : M * Nat.gcd 4 (q ^ b - 1) =
      (q ^ b) ^ 6 * (((q ^ b) ^ 2 - 1) * (((q ^ b) ^ 3 - 1) * ((q ^ b) ^ 4 - 1)))) :
    M * Nat.gcd 4 (q ^ b - 1) =
      q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) - 1) * (q ^ (4 * b) - 1))) := by
  rwa [show (q ^ b) ^ 6 = q ^ (6 * b) by rw [mul_comm, pow_mul],
    show (q ^ b) ^ 4 = q ^ (4 * b) by rw [mul_comm, pow_mul],
    show (q ^ b) ^ 3 = q ^ (3 * b) by rw [mul_comm, pow_mul],
    show (q ^ b) ^ 2 = q ^ (2 * b) by rw [mul_comm, pow_mul]] at h

private lemma norm_U4 {M q b : ℕ}
    (h : M * Nat.gcd 4 (q ^ b + 1) =
      (q ^ b) ^ 6 * (((q ^ b) ^ 2 - 1) * (((q ^ b) ^ 3 + 1) * ((q ^ b) ^ 4 - 1)))) :
    M * Nat.gcd 4 (q ^ b + 1) =
      q ^ (6 * b) * ((q ^ (2 * b) - 1) * ((q ^ (3 * b) + 1) * (q ^ (4 * b) - 1))) := by
  rwa [show (q ^ b) ^ 6 = q ^ (6 * b) by rw [mul_comm, pow_mul],
    show (q ^ b) ^ 4 = q ^ (4 * b) by rw [mul_comm, pow_mul],
    show (q ^ b) ^ 3 = q ^ (3 * b) by rw [mul_comm, pow_mul],
    show (q ^ b) ^ 2 = q ^ (2 * b) by rw [mul_comm, pow_mul]] at h

section Cert

private lemma factorization_of_order_eq {S : Type} [Group S] {t : StatedLieTag} {n q f : ℕ}
    (hq : q.Prime) (hadm : StatedLieAdmissible t n q f)
    (hcard : Nat.card S * lieOrderDivisor t n (q ^ f) = lieOrderNumerator t n (q ^ f)) :
    (Nat.card S).factorization q = lieSylowExponent t n * f := by
  have hN0 : lieOrderNumerator t n (q ^ f) ≠ 0 := by
    rw [CFSG.ComponentClassification.CatLeafProof.lieOrderNumerator_eq hadm]
    exact Nat.mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hq.ne_zero))
        (CFSG.ComponentClassification.CatLeafProof.lieOrderCofactor_ne_zero hadm)
  have hM0 : 0 < Nat.card S := by
    by_contra h
    have h0 : Nat.card S = 0 := by omega
    rw [h0, zero_mul] at hcard
    exact hN0 hcard.symm
  have hD0 : lieOrderDivisor t n (q ^ f) ≠ 0 :=
      CFSG.ComponentClassification.CatLeafProof.lieOrderDivisor_ne_zero hadm
  have hdvd : ¬ q ∣ lieOrderDivisor t n (q ^ f) :=
      CFSG.ComponentClassification.CatLeafProof.not_dvd_lieOrderDivisor hadm
  have hfac := congrArg (fun m => m.factorization q) hcard
  rw [Nat.factorization_mul hM0.ne' hD0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hdvd, add_zero,
    CFSG.ComponentClassification.CatLeafProof.factorization_lieOrderNumerator hadm] at hfac
  exact hfac

private lemma notJTypeOf_PSL2 {S : Type} [Group S] {q f : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hf : 1 ≤ f) (E1 : Nat.card S * 2 = q ^ f * (q ^ (2 * f) - 1)) (hF : (Nat.card
        S).factorization q = 1 * f) :
    ¬ JTypeOf S q := by
  rintro (⟨Q, hQp, hA | hA⟩ | ⟨Q, hQp, hB | hB | hB⟩)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_A2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 1 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_L2_A2 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_U3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 1 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_L2_U3_ratio hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_B2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 1 * f = 4 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_L2_B2 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_B2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_A3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 1 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_L2_A3 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_U4 Q hv e
    rw [hQp] at E2 F2
    have hrel : 1 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_L2_U4 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U4 E2)

private lemma notJTypeOf_OmegaOdd {S : Type} [Group S] {q f : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hf : 1 ≤ f) (E1 : Nat.card S * 2 = q ^ (9 * f) * ((q ^ (2 * f) - 1) * (q ^ (4 * f) - 1) *
        (q ^ (6 * f) - 1))) (hF : (Nat.card S).factorization q = 9 * f) :
    ¬ JTypeOf S q := by
  rintro (⟨Q, hQp, hA | hA⟩ | ⟨Q, hQp, hB | hB | hB⟩)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_A2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 9 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaOdd_A2 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_U3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 9 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaOdd_U3 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_B2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 9 * f = 4 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaOdd_B2 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_B2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_A3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 9 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaOdd_A3_secondary hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_U4 Q hv e
    rw [hQp] at E2 F2
    have hrel : 9 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaOdd_U4 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U4 E2)

private lemma notJTypeOf_OmegaPlus {S : Type} [Group S] {q f : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hf : 1 ≤ f) (E1 : Nat.card S * Nat.gcd 4 (q ^ (4 * f) - 1) = q ^ (12 * f) * ((q ^ (4 * f) -
        1) * ((q ^ (2 * f) - 1) * (q ^ (4 * f) - 1) * (q ^ (6 * f) - 1)))) (hF : (Nat.card
        S).factorization q = 12 * f) :
    ¬ JTypeOf S q := by
  rintro (⟨Q, hQp, hA | hA⟩ | ⟨Q, hQp, hB | hB | hB⟩)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_A2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaPlus_A2 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_U3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaPlus_U3 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_B2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 4 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaPlus_B2 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_B2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_A3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaPlus_A3 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_U4 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaPlus_U4 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U4 E2)

private lemma notJTypeOf_OmegaMinus {S : Type} [Group S] {q f : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hf : 1 ≤ f) (E1 : Nat.card S * Nat.gcd 4 (q ^ (4 * f) + 1) = q ^ (12 * f) * ((q ^ (4 * f) +
        1) * ((q ^ (2 * f) - 1) * (q ^ (4 * f) - 1) * (q ^ (6 * f) - 1)))) (hF : (Nat.card
        S).factorization q = 12 * f) :
    ¬ JTypeOf S q := by
  rintro (⟨Q, hQp, hA | hA⟩ | ⟨Q, hQp, hB | hB | hB⟩)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_A2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaMinus_A2 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_U3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaMinus_U3 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_B2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 4 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaMinus_B2 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_B2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_A3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaMinus_A3_ratio hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_U4 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_OmegaMinus_U4 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U4 E2)

private lemma notJTypeOf_G2 {S : Type} [Group S] {q f : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hf : 1 ≤ f) (E1 : Nat.card S * 1 = q ^ (6 * f) * ((q ^ (6 * f) - 1) * (q ^ (2 * f) - 1)))
        (hF : (Nat.card S).factorization q = 6 * f) :
    ¬ JTypeOf S q := by
  rintro (⟨Q, hQp, hA | hA⟩ | ⟨Q, hQp, hB | hB | hB⟩)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_A2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 6 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_G2_A2_ratio hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_U3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 6 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_G2_U3 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_B2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 6 * f = 4 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_G2_B2_ratio hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_B2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_A3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 6 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_G2_A3 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_U4 Q hv e
    rw [hQp] at E2 F2
    have hrel : 6 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_G2_U4_secondary hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U4 E2)

private lemma notJTypeOf_trialityD4 {S : Type} [Group S] {q f : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hf : 1 ≤ f) (E1 : Nat.card S * 1 = q ^ (12 * f) * ((q ^ (8 * f) + q ^ (4 * f) + 1) * ((q ^
        (6 * f) - 1) * (q ^ (2 * f) - 1)))) (hF : (Nat.card S).factorization q = 12 * f) :
    ¬ JTypeOf S q := by
  rintro (⟨Q, hQp, hA | hA⟩ | ⟨Q, hQp, hB | hB | hB⟩)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_A2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_trialityD4_A2_secondary hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hA
    obtain ⟨hb, E2, F2⟩ := orderEq_U3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 3 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_trialityD4_U3 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_B2 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 4 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_trialityD4_B2_ratio hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_B2 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_A3 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_trialityD4_A3 hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_A3 E2)
  · obtain ⟨hv, ⟨e⟩⟩ := catalogIs_onLie_eq hB
    obtain ⟨hb, E2, F2⟩ := orderEq_U4 Q hv e
    rw [hQp] at E2 F2
    have hrel : 12 * f = 6 * Q.exponent := by
      rw [← hF]; exact F2
    exact no_trialityD4_U4_secondary hq hq2 (by omega) Q.exponent_pos hrel E1 (norm_U4 E2)

theorem not_jType_of_card {G : Type} [Group G] [Finite G] {p q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {J : Subgroup G} {t : StatedLieTag} {n f : ℕ} (htn : NotJTypeTag t n) (hf : 1 ≤ f)
    (hcard : Nat.card (PSimple p J) * lieOrderDivisor t n (q ^ f) =
      lieOrderNumerator t n (q ^ f)) :
    ¬ JType p q J := by
  intro hJ
  rcases htn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl | rfl
  ·
    have hqodd : Odd q := hq.odd_of_ne_two hq2
    have hgcd : Nat.gcd 2 (q ^ f - 1) = 2 := gcd_two_pow_sub_one hqodd (by omega)
    have e2 : (q ^ f) ^ 2 = q ^ (2 * f) := by rw [← pow_mul, mul_comm]
    have E1 : Nat.card (PSimple p J) * 2 = q ^ f * (q ^ (2 * f) - 1) := by
      simp [lieOrderDivisor, lieOrderNumerator_PSL_two, hgcd] at hcard
      simpa [e2] using hcard
    by_cases h3 : q = 3 ∧ f = 1
    · rcases h3 with ⟨rfl, rfl⟩
      have hM : Nat.card (PSimple p J) = 12 := by
        simp [lieOrderDivisor, lieOrderNumerator_PSL_two] at hcard
        norm_num at hcard ⊢
        omega
      have hF : (Nat.card (PSimple p J)).factorization 3 = 1 * 1 := by
        have hM0 : 0 < Nat.card (PSimple p J) := by omega
        have hB0 : 0 < 3 ^ (2 * 1) - 1 := by norm_num
        have h := factorization_of_mul_eq (M := Nat.card (PSimple p J)) (q := 3)
          (A := 2) (B := 3 ^ (2 * 1) - 1) (e := 1) (by norm_num) (by simpa using E1)
          (by norm_num) (by norm_num) (by norm_num) hB0 hM0
        simpa using h
      exact notJTypeOf_PSL2 hq hq2 (by norm_num) E1 hF (jTypeOf_of_jType hJ)
    · have hadm : StatedLieAdmissible .PSL 2 q f := by
        refine ⟨hq, hf, by norm_num, ?_, ?_⟩
        · rintro h
          have h2 : q ^ f = 2 := by simpa using congrArg Prod.snd h
          have hqd : q ∣ 2 := by rw [← h2]; exact dvd_pow_self q (by omega)
          exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hqd)
        · rintro h
          have h3' : q ^ f = 3 := by simpa using congrArg Prod.snd h
          have hqd : q ∣ 3 := by rw [← h3']; exact dvd_pow_self q (by omega)
          have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hqd
          have hf1 : f = 1 := by
            rw [hq3] at h3'
            have hpow : (3 : ℕ) ^ f = 3 ^ 1 := by simpa using h3'
            exact pow_right_injective₀ (by norm_num) (by norm_num) hpow
          exact h3 ⟨hq3, hf1⟩
      have hF := factorization_of_order_eq (S := PSimple p J) hq hadm hcard
      exact notJTypeOf_PSL2 hq hq2 hf E1 (by simpa [lieSylowExponent] using hF)
        (jTypeOf_of_jType hJ)
  ·
    have hadm : StatedLieAdmissible .POmegaOdd 3 q f := by
      simp [StatedLieAdmissible, hq, hf, hq2]
    have hF := factorization_of_order_eq (S := PSimple p J) hq hadm hcard
    have e2 : (q ^ f) ^ 2 = q ^ (2 * f) := by rw [← pow_mul, mul_comm]
    have e4 : (q ^ f) ^ 4 = q ^ (4 * f) := by rw [← pow_mul, mul_comm]
    have e6 : (q ^ f) ^ 6 = q ^ (6 * f) := by rw [← pow_mul, mul_comm]
    have e9 : (q ^ f) ^ 9 = q ^ (9 * f) := by rw [← pow_mul, mul_comm]
    have E1 : Nat.card (PSimple p J) * 2 =
        q ^ (9 * f) * ((q ^ (2 * f) - 1) * (q ^ (4 * f) - 1) * (q ^ (6 * f) - 1)) := by
      simp [lieOrderDivisor,
        CFSG.ComponentClassification.HarrisLit.T1.RowLie.lieOrderNumerator_omega_three] at hcard
      simpa [e9, e2, e4, e6, mul_assoc] using hcard
    exact notJTypeOf_OmegaOdd hq hq2 hf E1 (by simpa [lieSylowExponent] using hF)
      (jTypeOf_of_jType hJ)
  ·
    have hadm : StatedLieAdmissible .POmegaPlus 4 q f := by
      simp [StatedLieAdmissible, hq, hf]
    have hF := factorization_of_order_eq (S := PSimple p J) hq hadm hcard
    have e2 : (q ^ f) ^ 2 = q ^ (2 * f) := by rw [← pow_mul, mul_comm]
    have e4 : (q ^ f) ^ 4 = q ^ (4 * f) := by rw [← pow_mul, mul_comm]
    have e6 : (q ^ f) ^ 6 = q ^ (6 * f) := by rw [← pow_mul, mul_comm]
    have e12 : (q ^ f) ^ 12 = q ^ (12 * f) := by rw [← pow_mul, mul_comm]
    have E1 : Nat.card (PSimple p J) * Nat.gcd 4 (q ^ (4 * f) - 1) =
        q ^ (12 * f) * ((q ^ (4 * f) - 1) *
          ((q ^ (2 * f) - 1) * (q ^ (4 * f) - 1) * (q ^ (6 * f) - 1))) := by
      simp [lieOrderDivisor, num_POmegaPlus] at hcard
      simpa [e12, e4, e2, e6] using hcard
    exact notJTypeOf_OmegaPlus hq hq2 hf E1 (by simpa [lieSylowExponent] using hF)
      (jTypeOf_of_jType hJ)
  ·
    have hadm : StatedLieAdmissible .POmegaMinus 4 q f := by
      simp [StatedLieAdmissible, hq, hf]
    have hF := factorization_of_order_eq (S := PSimple p J) hq hadm hcard
    have e2 : (q ^ f) ^ 2 = q ^ (2 * f) := by rw [← pow_mul, mul_comm]
    have e4 : (q ^ f) ^ 4 = q ^ (4 * f) := by rw [← pow_mul, mul_comm]
    have e6 : (q ^ f) ^ 6 = q ^ (6 * f) := by rw [← pow_mul, mul_comm]
    have e12 : (q ^ f) ^ 12 = q ^ (12 * f) := by rw [← pow_mul, mul_comm]
    have E1 : Nat.card (PSimple p J) * Nat.gcd 4 (q ^ (4 * f) + 1) =
        q ^ (12 * f) * ((q ^ (4 * f) + 1) *
          ((q ^ (2 * f) - 1) * (q ^ (4 * f) - 1) * (q ^ (6 * f) - 1))) := by
      simp [lieOrderDivisor, num_POmegaMinus] at hcard
      simpa [e12, e4, e2, e6] using hcard
    exact notJTypeOf_OmegaMinus hq hq2 hf E1 (by simpa [lieSylowExponent] using hF)
      (jTypeOf_of_jType hJ)
  ·
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    have h3le : 3 ≤ q ^ f := by
      calc 3 ≤ q := hq3
        _ = q ^ 1 := by ring
        _ ≤ q ^ f := Nat.pow_le_pow_right (by omega) hf
    have hadm : StatedLieAdmissible .G2 0 q f := by
      simp [StatedLieAdmissible, hq, hf, h3le]
    have hF := factorization_of_order_eq (S := PSimple p J) hq hadm hcard
    have e2 : (q ^ f) ^ 2 = q ^ (2 * f) := by rw [← pow_mul, mul_comm]
    have e6 : (q ^ f) ^ 6 = q ^ (6 * f) := by rw [← pow_mul, mul_comm]
    have E1 : Nat.card (PSimple p J) * 1 =
        q ^ (6 * f) * ((q ^ (6 * f) - 1) * (q ^ (2 * f) - 1)) := by
      simp [lieOrderDivisor, num_G2] at hcard
      simpa [e6, e2] using hcard
    exact notJTypeOf_G2 hq hq2 hf E1 (by simpa [lieSylowExponent] using hF)
      (jTypeOf_of_jType hJ)
  ·
    have hadm : StatedLieAdmissible .trialityD4 0 q f := by
      simp [StatedLieAdmissible, hq, hf]
    have hF := factorization_of_order_eq (S := PSimple p J) hq hadm hcard
    have e2 : (q ^ f) ^ 2 = q ^ (2 * f) := by rw [← pow_mul, mul_comm]
    have e4 : (q ^ f) ^ 4 = q ^ (4 * f) := by rw [← pow_mul, mul_comm]
    have e6 : (q ^ f) ^ 6 = q ^ (6 * f) := by rw [← pow_mul, mul_comm]
    have e8 : (q ^ f) ^ 8 = q ^ (8 * f) := by rw [← pow_mul, mul_comm]
    have e12 : (q ^ f) ^ 12 = q ^ (12 * f) := by rw [← pow_mul, mul_comm]
    have E1 : Nat.card (PSimple p J) * 1 =
        q ^ (12 * f) * ((q ^ (8 * f) + q ^ (4 * f) + 1) *
          ((q ^ (6 * f) - 1) * (q ^ (2 * f) - 1))) := by
      simp [lieOrderDivisor, num_trialityD4] at hcard
      simpa [e12, e8, e4, e6, e2] using hcard
    exact notJTypeOf_trialityD4 hq hq2 hf E1 (by simpa [lieSylowExponent] using hF)
      (jTypeOf_of_jType hJ)

theorem not_jType_of_lieModel {G : Type} [Group G] [Finite G] {p q : ℕ} (hq2 : q ≠ 2)
    {J : Subgroup G} {t : StatedLieTag} {n f : ℕ} (htn : NotJTypeTag t n)
    (hb : CFSG.Blueprint.LieModel (PSimple p J) t n q f) : ¬ JType p q J := by
  have hadm := CFSG.Blueprint.LieModel.admissible hb
  exact not_jType_of_card hadm.1 hq2 htn hadm.2.1 (raw_eq hb).1

theorem not_jType_of_statedClassicalModel {G : Type} [Group G] [Finite G] {p q : ℕ}
    (hq2 : q ≠ 2) {J : Subgroup G} {t : StatedLieTag} {n f : ℕ} (htn : NotJTypeTag t n)
    (hb : StatedClassicalModel (PSimple p J) t n q f) : ¬ JType p q J := by
  have hm : CFSG.Models.LieModel (PSimple p J) t n q f :=
    CFSG.Models.lieModel_of_statedClassicalModel hb
  by_cases ht : t ∈ CFSG.Blueprint.classicalTags
  · exact not_jType_of_lieModel hq2 htn
      (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel ht hm)
  · rcases htn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl | rfl
    all_goals simp [CFSG.Blueprint.classicalTags, StatedClassicalModel] at ht hb

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
