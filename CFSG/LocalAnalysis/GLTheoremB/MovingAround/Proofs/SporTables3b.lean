module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporTables3
import CFSG.HardMathSupport.Dickson.BMRows.M11Sylow

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables3

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Yardstones.Md0ec50421ce4 (PSimple IsChevSimple ambiguousChev)

namespace OrderDvdM

open CFSG.HardMathSupport.Solomon.Coordinator.I1420
open Finset

@[expose] def nM : ℕ := 66807960617346814440552399319272375000000

theorem nM_eq : nM = 2 ^ 6 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 *
    71 := by
  norm_num [nM]

@[expose] def primesM : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

@[expose] def qM : List ℕ := [2, 4, 8, 16, 32, 64, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049, 177147, 531441, 1594323, 4782969, 14348907, 43046721, 129140163, 387420489, 1162261467, 3486784401, 5, 25, 125, 625, 3125, 15625, 78125, 390625, 1953125, 7, 49, 343, 2401, 16807, 117649, 11, 13, 169, 2197, 17, 19, 23, 29, 31, 41, 47, 59, 71]

@[expose] def oddM : ℕ := 1043874384646043975633631239363630859375

theorem oddM_odd : Odd oddM := ⟨oddM / 2, by norm_num [oddM]⟩

theorem two_pow_six_mul_oddM : 2 ^ 6 * oddM = nM := by norm_num [oddM, nM]

@[expose] def Ok11 (v : ℕ) : Prop := v = 660 ∨ v = 6072 ∨ v = 32736

theorem prime_mem_primesM {p : ℕ} (hp : p.Prime) (h : p ∣ nM) : p ∈ primesM := by
  have hmem : p ∈ nM.primeFactorsList := (Nat.mem_primeFactorsList (by norm_num [nM])).2 ⟨hp, h⟩
  have hsub : ∀ x ∈ nM.primeFactorsList, x ∈ primesM := by
    unfold nM primesM
    simp only [Nat.primeFactorsList_ofNat]
    decide
  exact hsub p hmem

theorem prime_power_dvd_nM {q e : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (h : q ^ e ∣ nM) :
    q ∈ qM ∧ e ≤ 20 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  have hpp : p.Prime := hp
  have hpF : p ∣ nM :=
    (dvd_pow_self p (by omega : k ≠ 0)).trans ((dvd_pow_self (p ^ k) (by omega : e ≠ 0)).trans h)
  have h3 := prime_mem_primesM hpp hpF
  have hm : p ^ (k * e) ∣ nM := by rwa [pow_mul]
  have hlt : k * e < 136 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 136 ≤ 2 ^ (k * e) := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ (k * e) ≤ p ^ (k * e) := Nat.pow_le_pow_left hpp.two_le _
    have h3 : p ^ (k * e) ≤ nM := Nat.le_of_dvd (by norm_num [nM]) hm
    have h4 : nM < 2 ^ 136 := by norm_num [nM]
    omega
  have hkle : k ≤ k * e := Nat.le_mul_of_pos_right k he
  have hkF : p ^ k ∣ nM := (pow_dvd_pow p hkle).trans hm
  have key : ∀ p ∈ primesM, ∀ m < 136, p ^ m ∣ nM → m ≤ 20 := by
    unfold primesM nM
    decide +kernel
  have key2 : ∀ p ∈ primesM, ∀ m < 136, 1 ≤ m → p ^ m ∣ nM → p ^ m ∈ qM := by
    unfold primesM qM nM
    decide +kernel
  refine ⟨key2 p h3 k (by omega) hk hkF, ?_⟩
  have := key p h3 (k * e) hlt hm
  have h8 : e ≤ k * e := Nat.le_mul_of_pos_left e hk
  omega

theorem gen_bound {N G e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hG : Nat.Coprime q G) (hmul : G * N = q ^ e * R) (hN : N ∣ nM) : q ∈ qM ∧ e ≤ 20 := by
  have h1 : q ^ e ∣ G * nM := (Dvd.intro R hmul.symm).trans (mul_dvd_mul_left G hN)
  exact prime_power_dvd_nM hq he ((Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1)

theorem gen_bound' {N e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hmul : N = q ^ e * R) (hN : N ∣ nM) : q ∈ qM ∧ e ≤ 20 :=
  gen_bound hq he (Nat.coprime_one_right q) (by rw [one_mul]; exact hmul) hN

theorem orderA_ok {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) (h : orderA n q ∣ nM)
    (h11 : 11 ∣ orderA n q) : Ok11 (orderA n q) := by
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (q - 1) ∣ q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q - 1) * orderA n q =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hq5, he⟩ := gen_bound hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn2 : n ≤ 5 := by
    by_contra hc
    push Not at hc
    have : 21 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid1 : ∀ q ∈ qM, orderA 1 q ∣ nM → 11 ∣ orderA 1 q → Ok11 (orderA 1 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid2 : ∀ q ∈ qM, orderA 2 q ∣ nM → 11 ∣ orderA 2 q → Ok11 (orderA 2 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid3 : ∀ q ∈ qM, orderA 3 q ∣ nM → 11 ∣ orderA 3 q → Ok11 (orderA 3 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid4 : ∀ q ∈ qM, orderA 4 q ∣ nM → 11 ∣ orderA 4 q → Ok11 (orderA 4 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid5 : ∀ q ∈ qM, orderA 5 q ∣ nM → 11 ∣ orderA 5 q → Ok11 (orderA 5 q) := by
    unfold qM nM Ok11
    decide +kernel
  rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) with rfl | rfl | rfl | rfl | rfl
  · exact grid1 q hq5 h h11
  · exact grid2 q hq5 h h11
  · exact grid3 q hq5 h h11
  · exact grid4 q hq5 h h11
  · exact grid5 q hq5 h h11

theorem orderTwistedA_ok {n q : ℕ} (hn : 2 ≤ n) (hq : IsPrimePow q)
    (h : orderTwistedA n q ∣ nM) (h11 : 11 ∣ orderTwistedA n q) : Ok11 (orderTwistedA n q) := by
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
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hq5, he⟩ := gen_bound hq he1 (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  have hn2 : n ≤ 5 := by
    by_contra hc
    push Not at hc
    have : 21 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid2 : ∀ q ∈ qM, orderTwistedA 2 q ∣ nM → 11 ∣ orderTwistedA 2 q →
      Ok11 (orderTwistedA 2 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid3 : ∀ q ∈ qM, orderTwistedA 3 q ∣ nM → 11 ∣ orderTwistedA 3 q →
      Ok11 (orderTwistedA 3 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid4 : ∀ q ∈ qM, orderTwistedA 4 q ∣ nM → 11 ∣ orderTwistedA 4 q →
      Ok11 (orderTwistedA 4 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid5 : ∀ q ∈ qM, orderTwistedA 5 q ∣ nM → 11 ∣ orderTwistedA 5 q →
      Ok11 (orderTwistedA 5 q) := by
    unfold qM nM Ok11
    decide +kernel
  rcases (by omega : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) with rfl | rfl | rfl | rfl
  · exact grid2 q hq5 h h11
  · exact grid3 q hq5 h h11
  · exact grid4 q hq5 h h11
  · exact grid5 q hq5 h h11

theorem orderBC_ok {n q : ℕ} (hn : 2 ≤ n) (hq : IsPrimePow q) (h : orderBC n q ∣ nM)
    (h11 : 11 ∣ orderBC n q) : Ok11 (orderBC n q) := by
  have hq2 := hq.two_le
  have hmem : 1 ∈ Icc 1 n := by simp; omega
  have hfac : q - 1 ∣ (fun i => q ^ (2 * i) - 1) 1 := by
    show q - 1 ∣ q ^ (2 * 1) - 1
    exact Nat.sub_one_dvd_pow_sub_one q (2 * 1)
  have hGd : Nat.gcd 2 (q - 1) ∣ q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem)) _
  have hmul : Nat.gcd 2 (q - 1) * orderBC n q = q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * n := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨hq5, he⟩ := gen_bound hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn2 : n ≤ 4 := by nlinarith
  have grid2 : ∀ q ∈ qM, orderBC 2 q ∣ nM → 11 ∣ orderBC 2 q → Ok11 (orderBC 2 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid3 : ∀ q ∈ qM, orderBC 3 q ∣ nM → 11 ∣ orderBC 3 q → Ok11 (orderBC 3 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid4 : ∀ q ∈ qM, orderBC 4 q ∣ nM → 11 ∣ orderBC 4 q → Ok11 (orderBC 4 q) := by
    unfold qM nM Ok11
    decide +kernel
  rcases (by omega : n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl
  · exact grid2 q hq5 h h11
  · exact grid3 q hq5 h h11
  · exact grid4 q hq5 h h11

theorem orderD_ok {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) (h : orderD n q ∣ nM)
    (h11 : 11 ∣ orderD n q) : Ok11 (orderD n q) := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 4 (q ^ n - 1) ∣ q ^ (n * (n - 1)) * ((q ^ n - 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 (q ^ n - 1) * orderD n q = q ^ (n * (n - 1)) * ((q ^ n - 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    have h1 : q ^ (n * (n - 1)) * (q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) =
        q ^ (n * (n - 1)) * ((q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by ring
    unfold orderD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  obtain ⟨hq5, he⟩ := gen_bound hq (by omega)
    (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  have hn5 : n ≤ 5 := by
    by_contra hc
    push Not at hc
    have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid4 : ∀ q ∈ qM, orderD 4 q ∣ nM → 11 ∣ orderD 4 q → Ok11 (orderD 4 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid5 : ∀ q ∈ qM, orderD 5 q ∣ nM → 11 ∣ orderD 5 q → Ok11 (orderD 5 q) := by
    unfold qM nM Ok11
    decide +kernel
  rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
  · exact grid4 q hq5 h h11
  · exact grid5 q hq5 h h11

theorem orderTwistedD_ok {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) (h : orderTwistedD n q ∣ nM)
    (h11 : 11 ∣ orderTwistedD n q) : Ok11 (orderTwistedD n q) := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 4 (q ^ n + 1) ∣ q ^ (n * (n - 1)) * ((q ^ n + 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 (q ^ n + 1) * orderTwistedD n q = q ^ (n * (n - 1)) * ((q ^ n + 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    have h1 : q ^ (n * (n - 1)) * (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) =
        q ^ (n * (n - 1)) * ((q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by ring
    unfold orderTwistedD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  obtain ⟨hq5, he⟩ := gen_bound hq (by omega)
    (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  have hn5 : n ≤ 5 := by
    by_contra hc
    push Not at hc
    have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid4 : ∀ q ∈ qM, orderTwistedD 4 q ∣ nM → 11 ∣ orderTwistedD 4 q →
      Ok11 (orderTwistedD 4 q) := by
    unfold qM nM Ok11
    decide +kernel
  have grid5 : ∀ q ∈ qM, orderTwistedD 5 q ∣ nM → 11 ∣ orderTwistedD 5 q →
      Ok11 (orderTwistedD 5 q) := by
    unfold qM nM Ok11
    decide +kernel
  rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
  · exact grid4 q hq5 h h11
  · exact grid5 q hq5 h h11

theorem orderE6_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderE6 q ∣ nM := by
  intro h
  have hq2 := hq.two_le
  have hGd : Nat.gcd 3 (q - 1) ∣ q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
      (sub_one_dvd_sq_sub_one q)) _) _
  have hmul : Nat.gcd 3 (q - 1) * orderE6 q = q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderE6
    rw [show q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1)) = q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) by ring] at this ⊢
    exact this
  obtain ⟨-, he⟩ := gen_bound hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  omega

theorem orderTwistedE6_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderTwistedE6 q ∣ nM := by
  intro h
  have hq2 := hq.two_le
  have hGd : Nat.gcd 3 (q + 1) ∣ q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)) :=
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
  obtain ⟨-, he⟩ := gen_bound hq (by norm_num)
    (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  omega

theorem orderE7_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderE7 q ∣ nM := by
  intro h
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
  obtain ⟨-, he⟩ := gen_bound hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  omega

theorem orderE8_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderE8 q ∣ nM := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 120) (R := (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) *
    (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderE8; ring) h
  omega

theorem orderF4_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderF4 q ∣ nM := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 24) (R := (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1)) hq (by norm_num) (by unfold orderF4; ring) h
  omega

theorem orderG2_ok {q : ℕ} (hq : IsPrimePow q) (h : orderG2 q ∣ nM) (h11 : 11 ∣ orderG2 q) :
    Ok11 (orderG2 q) := by
  obtain ⟨hq5, -⟩ := gen_bound' (e := 6) (R := (q ^ 6 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderG2; ring) h
  have grid : ∀ q ∈ qM, orderG2 q ∣ nM → 11 ∣ orderG2 q → Ok11 (orderG2 q) := by
    unfold qM nM Ok11
    decide +kernel
  exact grid q hq5 h h11

theorem orderTrialityD4_ok {q : ℕ} (hq : IsPrimePow q) (h : orderTrialityD4 q ∣ nM)
    (h11 : 11 ∣ orderTrialityD4 q) : Ok11 (orderTrialityD4 q) := by
  obtain ⟨hq5, -⟩ := gen_bound' (e := 12) (R := (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1))
    hq (by norm_num) (by unfold orderTrialityD4; ring) h
  have grid : ∀ q ∈ qM, orderTrialityD4 q ∣ nM → 11 ∣ orderTrialityD4 q →
      Ok11 (orderTrialityD4 q) := by
    unfold qM nM Ok11
    decide +kernel
  exact grid q hq5 h h11

theorem orderSuzuki_ok {q : ℕ} (hq : IsPrimePow q) (h : orderSuzuki q ∣ nM)
    (h11 : 11 ∣ orderSuzuki q) : Ok11 (orderSuzuki q) := by
  obtain ⟨hq5, -⟩ := gen_bound' (e := 2) (R := (q ^ 2 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderSuzuki; ring) h
  have grid : ∀ q ∈ qM, orderSuzuki q ∣ nM → 11 ∣ orderSuzuki q → Ok11 (orderSuzuki q) := by
    unfold qM nM Ok11
    decide +kernel
  exact grid q hq5 h h11

theorem orderRee_ok {q : ℕ} (hq : IsPrimePow q) (h : orderRee q ∣ nM) (h11 : 11 ∣ orderRee q) :
    Ok11 (orderRee q) := by
  obtain ⟨hq5, -⟩ := gen_bound' (e := 3) (R := (q ^ 3 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderRee; ring) h
  have grid : ∀ q ∈ qM, orderRee q ∣ nM → 11 ∣ orderRee q → Ok11 (orderRee q) := by
    unfold qM nM Ok11
    decide +kernel
  exact grid q hq5 h h11

theorem orderTwistedF4_ok {q : ℕ} (hq : IsPrimePow q) (h : orderTwistedF4 q ∣ nM)
    (h11 : 11 ∣ orderTwistedF4 q) : Ok11 (orderTwistedF4 q) := by
  obtain ⟨hq5, -⟩ := gen_bound' (e := 12) (R := (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1))
    hq (by norm_num) (by unfold orderTwistedF4; ring) h
  have grid : ∀ q ∈ qM, orderTwistedF4 q ∣ nM → 11 ∣ orderTwistedF4 q →
      Ok11 (orderTwistedF4 q) := by
    unfold qM nM Ok11
    decide +kernel
  exact grid q hq5 h h11

theorem orderTits_dvd : ¬ orderTits ∣ nM := by
  unfold orderTits nM
  norm_num

theorem lieOrderFormula_dvd_nM {d : TauCeti.LieTypeIndex} (hd : d.Valid) (h : lieOrderFormula d ∣ nM)
    (h11 : 11 ∣ lieOrderFormula d) : Ok11 (lieOrderFormula d) := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q => exact orderA_ok hs.1 q.isPrimePow_card h h11
  | twistedA n q => exact orderTwistedA_ok hs.1 q.isPrimePow_card h h11
  | B n q => exact orderBC_ok hs.1 q.isPrimePow_card h h11
  | C n q => exact orderBC_ok (by have := hs.1; omega) q.isPrimePow_card h h11
  | D n q => exact orderD_ok hs q.isPrimePow_card h h11
  | twistedD n q => exact orderTwistedD_ok hs q.isPrimePow_card h h11
  | E6 q => exact absurd h (orderE6_dvd q.isPrimePow_card)
  | E7 q => exact absurd h (orderE7_dvd q.isPrimePow_card)
  | E8 q => exact absurd h (orderE8_dvd q.isPrimePow_card)
  | F4 q => exact absurd h (orderF4_dvd q.isPrimePow_card)
  | G2 q => exact orderG2_ok q.isPrimePow_card h h11
  | twistedE6 q => exact absurd h (orderTwistedE6_dvd q.isPrimePow_card)
  | trialityD4 q => exact orderTrialityD4_ok q.isPrimePow_card h h11
  | suzuki m => exact orderSuzuki_ok (Nat.prime_two.isPrimePow.pow (by omega)) h h11
  | reeG2 m => exact orderRee_ok (Nat.prime_three.isPrimePow.pow (by omega)) h h11
  | reeF4 m => exact orderTwistedF4_ok (Nat.prime_two.isPrimePow.pow (by omega)) h h11
  | tits => exact absurd h orderTits_dvd

end OrderDvdM

section S_not_isChevSimple_of_dvd_nM


theorem not_isChevSimple_of_dvd_nM (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] (h11 : 11 ∣ Nat.card T) (hd : Nat.card T ∣ OrderDvdM.nM)
    (h6072 : Nat.card T ≠ 6072) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq11 : q ≠ 11) :
    ¬ IsChevSimple q T := by
  intro hC
  have hlie : ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (T ≃* (TauCeti.CFSGIndex.lie d).Group) →
      Nat.card T = 660 ∨ Nat.card T = 32736 := by
    intro d ⟨e⟩
    have hn := hb d T ⟨e⟩
    rcases OrderDvdM.lieOrderFormula_dvd_nM d.2 (hn ▸ hd) (hn ▸ h11) with h | h | h
    · exact Or.inl (hn.trans h)
    · exact absurd (hn.trans h) h6072
    · exact Or.inr (hn.trans h)
  have hcases : Nat.card T = 660 ∨ Nat.card T = 32736 := by
    rcases hC with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    · cases i with
      | lie d => exact hlie d ⟨e⟩
      | _ => exact hi.elim
    · cases i with
      | lie d => exact hlie d ⟨e⟩
      | alternating n hn5 =>
        exfalso
        have hcn : Nat.card T = n.factorial / 2 :=
          (Nat.card_congr e.toEquiv).trans (Claims1116c.card_alt n (by omega))
        simp only [ambiguousChev] at hi
        rw [hcn] at h11
        rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> revert h11 <;> decide
      | _ => exact hi.elim
  rcases hcases with h | h
  · exact Claims1116c.not_isChevSimple_of_card_bound (p := 11) h (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide) q hq hq2 hq11 hC
  · exact Claims1116c.not_isChevSimple_of_card_bound (p := 11) h (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide) q hq hq2 hq11 hC

end S_not_isChevSimple_of_dvd_nM

theorem dvd_two_pow_mul_of_not_dvd {a m K k : ℕ} (hm : Odd m) (h : a ∣ 2 ^ K * m)
    (hk : ¬ 2 ^ (k + 1) ∣ a) : a ∣ 2 ^ k * m := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact hk (dvd_zero _)
  obtain ⟨j, a', ha', rfl⟩ := Nat.exists_eq_two_pow_mul_odd ha
  have hj : j ≤ k := by
    by_contra hj
    push Not at hj
    exact hk (Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega : k + 1 ≤ j)) a')
  have h1 : a' ∣ 2 ^ K * m := (Dvd.intro_left _ rfl).trans h
  have ha'm : a' ∣ m := (Nat.Coprime.pow_right K ha'.coprime_two_right).dvd_of_dvd_mul_left h1
  exact mul_dvd_mul (pow_dvd_pow 2 hj) ha'm

section ResidualsEleven

open CFSG.AGLEmbedding.Norton.MON5_7 (gw)
open CFSG.AGLEmbedding.Norton.Gen11 (gen11W0)
open CFSG.Monster.Generated (Gmat)

@[expose] def MElevenNoL223 : Prop :=
  ∀ I : Subgroup Gmat, GLAPComponent 11 (Subgroup.centralizer ({gw gen11W0} : Set Gmat)) I →
    Nat.card (PSimple 11 I) ≠ 6072

@[expose] def MElevenNo23 : Prop :=
  ¬ 23 ∣ Nat.card ↥(Subgroup.centralizer ({gw gen11W0} : Set Gmat))

end ResidualsEleven

section S_mElevenNoL223_of_no23


open CFSG.AGLEmbedding.Norton.MON5_7 (gw) in
open CFSG.AGLEmbedding.Norton.Gen11 (gen11W0) in
open CFSG.Monster.Generated (Gmat) in
theorem mElevenNoL223_of_no23 (h : MElevenNo23) : MElevenNoL223 := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  intro I hI h6
  apply h
  have hmul := Inputs1419b.mul_card_pSimple_dvd (by norm_num)
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal.orderOf_x11 hI
  rw [h6] at hmul
  exact (show 23 ∣ 11 * 6072 by norm_num).trans hmul

end S_mElevenNoL223_of_no23

section S_mElevenDown_of_noL223


open CFSG.AGLEmbedding.Norton.MON5_7 (gw) in
open CFSG.AGLEmbedding.Norton.Gen11 (gen11W0) in
open CFSG.Monster.Generated (Gmat) in
theorem mElevenDown_of_noL223 (h : MElevenNoL223) : SporTables2.MElevenDown := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  have hx := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal.orderOf_x11
  have h2 := CFSG.HardMathSupport.Dickson.BMRows.M11.not_two_pow_seven_dvd_card_centralizer_x11
  have hG : Nat.card Gmat = 11 * (2 ^ 46 * OrderDvdM.oddM) := by
    rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
    norm_num [CFSG.Open.monsterOrder, OrderDvdM.oddM]
  intro I hI
  refine Claims1116c.downTypeOK_of_not_chev fun q hq hq2 hq11 => ?_
  have h11 := Claims1116d.prime_dvd_card_pSimple (by norm_num : Nat.Prime 11) hI
  have hmul := Inputs1419b.mul_card_pSimple_dvd (by norm_num) hx hI
  have hCG : Nat.card ↥(Subgroup.centralizer ({gw gen11W0} : Set Gmat)) ∣ Nat.card Gmat :=
    Subgroup.card_subgroup_dvd_card _
  have hT1 : Nat.card (PSimple 11 I) ∣ 2 ^ 46 * OrderDvdM.oddM := by
    have := hmul.trans hCG
    rw [hG] at this
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hT2 : ¬ 2 ^ (6 + 1) ∣ Nat.card (PSimple 11 I) := fun h7 =>
    h2 (h7.trans ((Dvd.intro_left 11 rfl).trans hmul))
  have hd : Nat.card (PSimple 11 I) ∣ OrderDvdM.nM := by
    rw [← OrderDvdM.two_pow_six_mul_oddM]
    exact dvd_two_pow_mul_of_not_dvd OrderDvdM.oddM_odd hT1 hT2
  exact not_isChevSimple_of_dvd_nM CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds h11 hd
    (h I hI) hq hq2 hq11

end S_mElevenDown_of_noL223

section Connectors

open CFSG.AGLEmbedding.Norton.MON5_7 (gw)
open CFSG.AGLEmbedding.Norton.Gen11 (gen11W0)
open CFSG.Monster.Generated (Gmat)

theorem mElevenNoL223_of_shapeRkAt {Good Rk : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.ShapeRkAt 11 Good Rk (gw gen11W0))
    (hG : ∀ (T : Type) [Group T], Good T → Nat.card T ≠ 6072) : MElevenNoL223 := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  intro I hI
  rcases h with hc | ⟨J, -, hu, hg, -⟩
  · exact (CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape (by norm_num) hc
      hI).elim
  · rw [hu I hI]
    exact hG _ hg

theorem mElevenNoL223_of_card (h : ∀ I : Subgroup Gmat, GLAPComponent 11 (Subgroup.centralizer
      ({gw gen11W0} : Set Gmat)) I → Nat.card (PSimple 11 I) = 95040) : MElevenNoL223 :=
  fun I hI h6 => by
    rw [h I hI] at h6
    norm_num at h6

end Connectors

section Structure4


structure SporDownResidual4 : Prop where
  B_three : CFSG.HardMathSupport.Dickson.I271.TabBThreeBNoComp
  M_three : CFSG.HardMathSupport.Dickson.I271.M3ResBNoComp
  B_five : CFSG.HardMathSupport.Dickson.I271.TabBFiveBNoComp
  M_five : CFSG.HardMathSupport.Dickson.I271.CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M)
  M_eleven : MElevenNoL223

end Structure4

section S_sporDownResidual3_of_residual4


theorem sporDownResidual3_of_residual4 (h : SporDownResidual4) : SporDownResidual3 where
  B_three := h.B_three
  M_three := h.M_three
  B_five := h.B_five
  M_five := h.M_five
  M_eleven := mElevenDown_of_noL223 h.M_eleven

end S_sporDownResidual3_of_residual4

section S_sporDownResidualPP_of_residual4


theorem sporDownResidual''_of_residual4
    (h : SporDownResidual4) : SporTables2.SporDownResidual'' :=
  sporDownResidual''_of_residual3 (sporDownResidual3_of_residual4 h)

end S_sporDownResidualPP_of_residual4

section S_sporDownResidualP_of_residual4


theorem sporDownResidual'_of_residual4
    (h : SporDownResidual4) : Claims1116d.SporDownResidual' :=
  sporDownResidual'_of_residual3 (sporDownResidual3_of_residual4 h)

end S_sporDownResidualP_of_residual4

section S_inputSporDownChev_of_residual4


theorem inputSporDownChev_of_residual4
    (h : SporDownResidual4) : Claims1116b.InputSporDownChev :=
  inputSporDownChev_of_residual3 (sporDownResidual3_of_residual4 h)

end S_inputSporDownChev_of_residual4

section S_sporDownResidualK_of_noL223


theorem sporDownResidualK_of_noL223
    (h : MElevenNoL223) : SporTables2.SporDownResidualK :=
  sporDownResidualK_of_mElevenDown (mElevenDown_of_noL223 h)

end S_sporDownResidualK_of_noL223

section S_sporDownResidualP_of_noL223_kGroup


theorem sporDownResidual'_of_noL223_kGroup
    (hB : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group)
    (hM : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) (h : MElevenNoL223) :
    Claims1116d.SporDownResidual' :=
  sporDownResidual'_of_mElevenDown_kGroup hB hM (mElevenDown_of_noL223 h)

end S_sporDownResidualP_of_noL223_kGroup

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables3

end
