module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator.I1420
open Finset

@[expose] def fi24Ord : ℕ := 1255205709190661721292800

@[expose] def primesFi24 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 23, 29]

@[expose] def qFi24 : List ℕ :=
  [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
    131072, 262144, 524288, 1048576, 2097152,
    3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049, 177147, 531441, 1594323, 4782969,
    14348907, 43046721, 5, 25, 7, 49, 343, 11, 13, 17, 23, 29]

theorem prime_mem_primesFi24 {p : ℕ} (hp : p.Prime) (h : p ∣ fi24Ord) : p ∈ primesFi24 := by
  have hmem : p ∈ fi24Ord.primeFactorsList :=
    (Nat.mem_primeFactorsList (by norm_num [fi24Ord])).2 ⟨hp, h⟩
  have hsub : ∀ x ∈ fi24Ord.primeFactorsList, x ∈ primesFi24 := by
    unfold fi24Ord primesFi24
    simp only [Nat.primeFactorsList_ofNat]
    decide
  exact hsub p hmem

theorem prime_power_dvd_fi24Ord {q e : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (h : q ^ e ∣ fi24Ord) : q ∈ qFi24 ∧ e ≤ 21 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  have hpp : p.Prime := hp
  have hpF : p ∣ fi24Ord :=
    (dvd_pow_self p (by omega : k ≠ 0)).trans
      ((dvd_pow_self (p ^ k) (by omega : e ≠ 0)).trans h)
  have h3 := prime_mem_primesFi24 hpp hpF
  have hm : p ^ (k * e) ∣ fi24Ord := by rwa [pow_mul]
  have hlt : k * e < 81 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 81 ≤ 2 ^ (k * e) := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ (k * e) ≤ p ^ (k * e) := Nat.pow_le_pow_left hpp.two_le _
    have h3 : p ^ (k * e) ≤ fi24Ord := Nat.le_of_dvd (by norm_num [fi24Ord]) hm
    have h4 : fi24Ord < 2 ^ 81 := by norm_num [fi24Ord]
    omega
  have hkle : k ≤ k * e := Nat.le_mul_of_pos_right k he
  have hkF : p ^ k ∣ fi24Ord := (pow_dvd_pow p hkle).trans hm
  have key : ∀ p ∈ primesFi24, ∀ m < 81, p ^ m ∣ fi24Ord → m ≤ 21 := by
    unfold primesFi24 fi24Ord
    decide +kernel
  have key2 : ∀ p ∈ primesFi24, ∀ m < 81, 1 ≤ m → p ^ m ∣ fi24Ord → p ^ m ∈ qFi24 := by
    unfold primesFi24 qFi24 fi24Ord
    decide +kernel
  refine ⟨key2 p h3 k (by omega) hk hkF, ?_⟩
  have := key p h3 (k * e) hlt hm
  have h8 : e ≤ k * e := Nat.le_mul_of_pos_left e hk
  omega

theorem gen_bound_fi24 {N G e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hG : Nat.Coprime q G) (hmul : G * N = q ^ e * R) (hN : N ∣ fi24Ord) :
    q ∈ qFi24 ∧ e ≤ 21 := by
  have h1 : q ^ e ∣ G * fi24Ord := (Dvd.intro R hmul.symm).trans (mul_dvd_mul_left G hN)
  exact prime_power_dvd_fi24Ord hq he ((Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1)

theorem gen_bound_fi24' {N e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hmul : N = q ^ e * R) (hN : N ∣ fi24Ord) : q ∈ qFi24 ∧ e ≤ 21 :=
  gen_bound_fi24 hq he (Nat.coprime_one_right q) (by rw [one_mul]; exact hmul) hN

theorem card_of_iso_cyclic {L : Type} [Group L] {r : ℕ} (hr : r.Prime)
    (e : L ≃* (TauCeti.CFSGIndex.cyclic r hr).Group) : Nat.card L = r := by
  rw [Nat.card_congr e.toEquiv]
  show Nat.card (Multiplicative (ZMod r)) = r
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem not_nineteen_dvd_fi24Ord : ¬ 19 ∣ fi24Ord := by
  norm_num [fi24Ord]

theorem not_seven_cube_dvd_factorial_div_two {n : ℕ} (hn5 : 5 ≤ n) (hn20 : n ≤ 20) :
    ¬ 7 ^ 3 ∣ n.factorial / 2 := by
  have hgrid : ∀ n ∈ ([5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] : List ℕ),
      ¬ 7 ^ 3 ∣ n.factorial / 2 := by
    decide +kernel
  exact hgrid n (by simp; omega)

theorem le_twenty_one_of_seven_cube_dvd_factorial_div_two {n : ℕ} (hn : 5 ≤ n)
    (h7 : 7 ^ 3 ∣ n.factorial / 2) : 21 ≤ n := by
  by_contra h
  push Not at h
  exact not_seven_cube_dvd_factorial_div_two hn (by omega) h7

theorem nineteen_dvd_factorial_div_two {n : ℕ} (hn : 21 ≤ n) : 19 ∣ n.factorial / 2 := by
  have h2 : 2 ∣ n.factorial := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 2)).2 (by omega)
  have hmul : n.factorial / 2 * 2 = n.factorial := Nat.div_mul_cancel h2
  have h19 : 19 ∣ n.factorial :=
    (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 19)).2 (by omega)
  exact (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num : Nat.Coprime 19 2)
    (by rw [hmul]; exact h19))

theorem sporOrd_eq_He_or_fi24Ord {s : TauCeti.SporadicName}
    (h : sporOrd s ∣ fi24Ord ∧ 7 ^ 3 ∣ sporOrd s) :
    sporOrd s = 4030387200 ∨ sporOrd s = fi24Ord := by
  have key : ∀ s : TauCeti.SporadicName, sporOrd s ∣ fi24Ord → 7 ^ 3 ∣ sporOrd s →
      sporOrd s = 4030387200 ∨ sporOrd s = fi24Ord := by
    intro s
    cases s <;> decide +kernel
  exact key s h.1 h.2

theorem orderA_not_seven_cube {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q)
    (h : orderA n q ∣ fi24Ord) (h7 : 7 ^ 3 ∣ orderA n q) : False := by
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (q - 1) ∣
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q - 1) * orderA n q =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hqmem, he⟩ := gen_bound_fi24 hq he1
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  have hn6 : n ≤ 6 := by
    by_contra hc
    push Not at hc
    have : 28 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ n ∈ ([1, 2, 3, 4, 5, 6] : List ℕ), ∀ q ∈ qFi24,
      ¬ (orderA n q ∣ fi24Ord ∧ 7 ^ 3 ∣ orderA n q) := by
    unfold qFi24 fi24Ord
    decide +kernel
  exact grid n (by simp; omega) q hqmem ⟨h, h7⟩

theorem orderTwistedA_not_seven_cube {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q)
    (h : orderTwistedA n q ∣ fi24Ord) (h7 : 7 ^ 3 ∣ orderTwistedA n q) : False := by
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hfac : q + 1 ∣ (fun i => if Even i then q ^ i - 1 else q ^ i + 1) 2 := by
    show q + 1 ∣ (if Even 2 then q ^ 2 - 1 else q ^ 2 + 1)
    simpa using add_one_dvd_sq_sub_one q (by omega)
  have hGd : Nat.gcd (n + 1) (q + 1) ∣ q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q + 1) * orderTwistedA n q = q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) :=
    Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hqmem, he⟩ := gen_bound_fi24 hq he1
    (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  have hn6 : n ≤ 6 := by
    by_contra hc
    push Not at hc
    have : 28 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ n ∈ ([1, 2, 3, 4, 5, 6] : List ℕ), ∀ q ∈ qFi24,
      ¬ (orderTwistedA n q ∣ fi24Ord ∧ 7 ^ 3 ∣ orderTwistedA n q) := by
    unfold qFi24 fi24Ord
    decide +kernel
  exact grid n (by simp; omega) q hqmem ⟨h, h7⟩

theorem orderBC_not_seven_cube {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q)
    (h : orderBC n q ∣ fi24Ord) (h7 : 7 ^ 3 ∣ orderBC n q) : False := by
  have hq2 := hq.two_le
  have hmem : 1 ∈ Icc 1 n := by simp; omega
  have hfac : q - 1 ∣ (fun i => q ^ (2 * i) - 1) 1 := by
    show q - 1 ∣ q ^ (2 * 1) - 1
    exact Nat.sub_one_dvd_pow_sub_one q (2 * 1)
  have hGd : Nat.gcd 2 (q - 1) ∣ q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem)) _
  have hmul : Nat.gcd 2 (q - 1) * orderBC n q =
      q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * n := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨hqmem, he⟩ := gen_bound_fi24 hq he1
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  have hn4 : n ≤ 4 := by nlinarith
  have grid : ∀ n ∈ ([1, 2, 3, 4] : List ℕ), ∀ q ∈ qFi24,
      ¬ (orderBC n q ∣ fi24Ord ∧ 7 ^ 3 ∣ orderBC n q) := by
    unfold qFi24 fi24Ord
    decide +kernel
  exact grid n (by simp; omega) q hqmem ⟨h, h7⟩

theorem orderD_not_seven_cube {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q)
    (h : orderD n q ∣ fi24Ord) (h7 : 7 ^ 3 ∣ orderD n q) : False := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 4 (q ^ n - 1) ∣ q ^ (n * (n - 1)) * ((q ^ n - 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 (q ^ n - 1) * orderD n q = q ^ (n * (n - 1)) * ((q ^ n - 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    have h1 : q ^ (n * (n - 1)) * (q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) =
        q ^ (n * (n - 1)) * ((q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
      ring
    unfold orderD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n - 1) := by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  obtain ⟨hqmem, he⟩ := gen_bound_fi24 hq he1
    (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  have hn5 : n ≤ 5 := by
    by_contra hc
    push Not at hc
    have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid : ∀ n ∈ ([4, 5] : List ℕ), ∀ q ∈ qFi24,
      ¬ (orderD n q ∣ fi24Ord ∧ 7 ^ 3 ∣ orderD n q) := by
    unfold qFi24 fi24Ord
    decide +kernel
  exact grid n (by simp; omega) q hqmem ⟨h, h7⟩

theorem orderTwistedD_not_seven_cube {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q)
    (h : orderTwistedD n q ∣ fi24Ord) (h7 : 7 ^ 3 ∣ orderTwistedD n q) : False := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 4 (q ^ n + 1) ∣ q ^ (n * (n - 1)) * ((q ^ n + 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 (q ^ n + 1) * orderTwistedD n q = q ^ (n * (n - 1)) *
      ((q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    have h1 : q ^ (n * (n - 1)) * (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) =
        q ^ (n * (n - 1)) * ((q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
      ring
    unfold orderTwistedD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n - 1) := by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  obtain ⟨hqmem, he⟩ := gen_bound_fi24 hq he1
    (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  have hn5 : n ≤ 5 := by
    by_contra hc
    push Not at hc
    have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid : ∀ n ∈ ([4, 5] : List ℕ), ∀ q ∈ qFi24,
      ¬ (orderTwistedD n q ∣ fi24Ord ∧ 7 ^ 3 ∣ orderTwistedD n q) := by
    unfold qFi24 fi24Ord
    decide +kernel
  exact grid n (by simp; omega) q hqmem ⟨h, h7⟩

theorem orderE6_not_seven_cube {q : ℕ} (hq : IsPrimePow q)
    (h : orderE6 q ∣ fi24Ord) : False := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 3 (q - 1) ∣ q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
      (sub_one_dvd_sq_sub_one q)) _) _
  have hmul : Nat.gcd 3 (q - 1) * orderE6 q = q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderE6
    rw [show q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1)) = q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) by ring] at this ⊢
    exact this
  obtain ⟨-, he⟩ := gen_bound_fi24 hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  omega

theorem orderTwistedE6_not_seven_cube {q : ℕ} (hq : IsPrimePow q)
    (h : orderTwistedE6 q ∣ fi24Ord) : False := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 3 (q + 1) ∣ q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
      (add_one_dvd_sq_sub_one q (by omega))) _) _
  have hmul : Nat.gcd 3 (q + 1) * orderTwistedE6 q = q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderTwistedE6
    rw [show q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1)) = q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) by ring] at this ⊢
    exact this
  obtain ⟨-, he⟩ := gen_bound_fi24 hq (by norm_num)
    (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  omega

theorem orderE7_not_seven_cube {q : ℕ} (hq : IsPrimePow q)
    (h : orderE7 q ∣ fi24Ord) : False := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 2 (q - 1) ∣ q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
      (sub_one_dvd_sq_sub_one q)) _) _
  have hmul : Nat.gcd 2 (q - 1) * orderE7 q = q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) *
      (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderE7
    rw [show q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 2 - 1)) = q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) by ring] at this ⊢
    exact this
  obtain ⟨-, he⟩ := gen_bound_fi24 hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  omega

theorem orderE8_not_seven_cube {q : ℕ} (hq : IsPrimePow q)
    (h : orderE8 q ∣ fi24Ord) : False := by
  obtain ⟨-, he⟩ := gen_bound_fi24' (e := 120)
    (R := (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
      (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderE8; ring) h
  omega

theorem orderF4_not_seven_cube {q : ℕ} (hq : IsPrimePow q)
    (h : orderF4 q ∣ fi24Ord) : False := by
  obtain ⟨-, he⟩ := gen_bound_fi24' (e := 24)
    (R := (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderF4; ring) h
  omega

theorem orderG2_not_seven_cube {q : ℕ} (hq : IsPrimePow q)
    (h : orderG2 q ∣ fi24Ord) (h7 : 7 ^ 3 ∣ orderG2 q) : False := by
  obtain ⟨hqmem, -⟩ := gen_bound_fi24' (e := 6) (R := (q ^ 6 - 1) * (q ^ 2 - 1))
    hq (by norm_num) (by unfold orderG2; ring) h
  have grid : ∀ q ∈ qFi24, ¬ (orderG2 q ∣ fi24Ord ∧ 7 ^ 3 ∣ orderG2 q) := by
    unfold qFi24 fi24Ord
    decide +kernel
  exact grid q hqmem ⟨h, h7⟩

theorem orderTrialityD4_not_seven_cube {q : ℕ} (hq : IsPrimePow q)
    (h : orderTrialityD4 q ∣ fi24Ord) (h7 : 7 ^ 3 ∣ orderTrialityD4 q) : False := by
  obtain ⟨hqmem, -⟩ := gen_bound_fi24' (e := 12)
    (R := (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderTrialityD4; ring) h
  have grid : ∀ q ∈ qFi24, ¬ (orderTrialityD4 q ∣ fi24Ord ∧ 7 ^ 3 ∣ orderTrialityD4 q) := by
    unfold qFi24 fi24Ord
    decide +kernel
  exact grid q hqmem ⟨h, h7⟩

theorem orderSuzuki_not_seven_cube {q : ℕ} (hq : IsPrimePow q)
    (h : orderSuzuki q ∣ fi24Ord) (h7 : 7 ^ 3 ∣ orderSuzuki q) : False := by
  obtain ⟨hqmem, -⟩ := gen_bound_fi24' (e := 2) (R := (q ^ 2 + 1) * (q - 1))
    hq (by norm_num) (by unfold orderSuzuki; ring) h
  have grid : ∀ q ∈ qFi24, ¬ (orderSuzuki q ∣ fi24Ord ∧ 7 ^ 3 ∣ orderSuzuki q) := by
    unfold qFi24 fi24Ord
    decide +kernel
  exact grid q hqmem ⟨h, h7⟩

theorem orderRee_not_seven_cube {q : ℕ} (hq : IsPrimePow q)
    (h : orderRee q ∣ fi24Ord) (h7 : 7 ^ 3 ∣ orderRee q) : False := by
  obtain ⟨hqmem, -⟩ := gen_bound_fi24' (e := 3) (R := (q ^ 3 + 1) * (q - 1))
    hq (by norm_num) (by unfold orderRee; ring) h
  have grid : ∀ q ∈ qFi24, ¬ (orderRee q ∣ fi24Ord ∧ 7 ^ 3 ∣ orderRee q) := by
    unfold qFi24 fi24Ord
    decide +kernel
  exact grid q hqmem ⟨h, h7⟩

theorem orderTwistedF4_not_seven_cube {q : ℕ} (hq : IsPrimePow q)
    (h : orderTwistedF4 q ∣ fi24Ord) (h7 : 7 ^ 3 ∣ orderTwistedF4 q) : False := by
  obtain ⟨hqmem, -⟩ := gen_bound_fi24' (e := 12)
    (R := (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderTwistedF4; ring) h
  have grid : ∀ q ∈ qFi24,
      ¬ (orderTwistedF4 q ∣ fi24Ord ∧ 7 ^ 3 ∣ orderTwistedF4 q) := by
    unfold qFi24 fi24Ord
    decide +kernel
  exact grid q hqmem ⟨h, h7⟩

theorem orderTits_not_seven_cube : ¬ 7 ^ 3 ∣ orderTits := by
  unfold orderTits
  norm_num

theorem lieOrderFormula_not_seven_cube {d : TauCeti.LieTypeIndex} (hd : d.Valid)
    (h : lieOrderFormula d ∣ fi24Ord) (h7 : 7 ^ 3 ∣ lieOrderFormula d) : False := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q =>
    exact orderA_not_seven_cube (n := n) (q := q.card) hs.1 q.isPrimePow_card h h7
  | twistedA n q =>
    have hn : 1 ≤ n := by have := hs.1; omega
    exact orderTwistedA_not_seven_cube (n := n) (q := q.card) hn q.isPrimePow_card h h7
  | B n q =>
    have hn : 1 ≤ n := by have := hs.1; omega
    exact orderBC_not_seven_cube (n := n) (q := q.card) hn q.isPrimePow_card h h7
  | C n q =>
    have hn : 1 ≤ n := by have := hs.1; omega
    exact orderBC_not_seven_cube (n := n) (q := q.card) hn q.isPrimePow_card h h7
  | D n q =>
    exact orderD_not_seven_cube (n := n) (q := q.card) hs q.isPrimePow_card h h7
  | twistedD n q =>
    exact orderTwistedD_not_seven_cube (n := n) (q := q.card) hs q.isPrimePow_card h h7
  | E6 q =>
    exact orderE6_not_seven_cube (q := q.card) q.isPrimePow_card h
  | E7 q =>
    exact orderE7_not_seven_cube (q := q.card) q.isPrimePow_card h
  | E8 q =>
    exact orderE8_not_seven_cube (q := q.card) q.isPrimePow_card h
  | F4 q =>
    exact orderF4_not_seven_cube (q := q.card) q.isPrimePow_card h
  | G2 q =>
    exact orderG2_not_seven_cube (q := q.card) q.isPrimePow_card h h7
  | twistedE6 q =>
    exact orderTwistedE6_not_seven_cube (q := q.card) q.isPrimePow_card h
  | trialityD4 q =>
    exact orderTrialityD4_not_seven_cube (q := q.card) q.isPrimePow_card h h7
  | suzuki m =>
    exact orderSuzuki_not_seven_cube (Nat.prime_two.isPrimePow.pow (by omega)) h h7
  | reeG2 m =>
    exact orderRee_not_seven_cube (Nat.prime_three.isPrimePow.pow (by omega)) h h7
  | reeF4 m =>
    exact orderTwistedF4_not_seven_cube (Nat.prime_two.isPrimePow.pow (by omega)) h h7
  | tits =>
    exact orderTits_not_seven_cube h7

theorem card_eq_of_isCatalogGroup_of_dvd (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsCatalogGroup L)
    (hd : Nat.card L ∣ 1255205709190661721292800) (h7 : 7 ^ 3 ∣ Nat.card L) :
    Nat.card L = 4030387200 ∨ Nat.card L = 1255205709190661721292800 := by
  obtain ⟨i, ⟨e⟩⟩ := hL
  have hd' : Nat.card L ∣ fi24Ord := hd
  cases i with
  | cyclic r hr =>
    exfalso
    have hcard : Nat.card L = r := card_of_iso_cyclic hr e
    have h7r : 7 ^ 3 ∣ r := by
      rw [hcard] at h7
      exact h7
    rcases (Nat.dvd_prime hr).mp h7r with h | h
    · norm_num at h
    · rw [← h] at hr
      norm_num at hr
  | alternating n hn =>
    exfalso
    have hcard : Nat.card L = n.factorial / 2 :=
      CFSG.LocalAnalysis.GLTheoremA.CatDistinct.card_alternating_of_iso hn e
    have h7f : 7 ^ 3 ∣ n.factorial / 2 := by
      rw [hcard] at h7
      exact h7
    have hn21 : 21 ≤ n := le_twenty_one_of_seven_cube_dvd_factorial_div_two hn h7f
    have h19 : 19 ∣ n.factorial / 2 := nineteen_dvd_factorial_div_two hn21
    have hd2 : n.factorial / 2 ∣ fi24Ord := by
      rw [hcard] at hd'
      exact hd'
    exact not_nineteen_dvd_fi24Ord (h19.trans hd2)
  | sporadic s =>
    have hcard : Nat.card L = sporOrd s := by
      rw [Nat.card_congr e.toEquiv]
      exact hOrd s
    have hd2 : sporOrd s ∣ fi24Ord := by
      rw [hcard] at hd'
      exact hd'
    have h7s : 7 ^ 3 ∣ sporOrd s := by
      rw [hcard] at h7
      exact h7
    have h := sporOrd_eq_He_or_fi24Ord ⟨hd2, h7s⟩
    rwa [hcard]
  | lie d =>
    exfalso
    have hcard : Nat.card L = lieOrderFormula d.1 := hb d L ⟨e⟩
    have hd2 : lieOrderFormula d.1 ∣ fi24Ord := by
      rw [hcard] at hd'
      exact hd'
    have h7l : 7 ^ 3 ∣ lieOrderFormula d.1 := by
      rw [hcard] at h7
      exact h7
    exact lieOrderFormula_not_seven_cube d.2 hd2 h7l

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
