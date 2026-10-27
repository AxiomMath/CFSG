module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows.Order504

open CFSG.HardMathSupport.Solomon.Coordinator.I1420

section OrderBounds

open CFSG.Open Finset

private def q6 : List ℕ := [2, 4, 8, 3, 9, 7]

private theorem prime_power_dvd_504 {q e : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (h : q ^ e ∣ 504) : q ∈ q6 ∧ e ≤ 3 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  have hpp : p.Prime := hp
  have hpF : p ∣ 504 :=
    (dvd_pow_self p (by omega : k ≠ 0)).trans ((dvd_pow_self (p ^ k) (by omega : e ≠ 0)).trans h)
  have h3 : p ∈ ([2, 3, 7] : List ℕ) := by
    have h504 : (504 : ℕ) = 2 ^ 3 * 3 ^ 2 * 7 := by norm_num
    rw [h504] at hpF
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases (Nat.Prime.dvd_mul hpp).1 hpF with h1 | h1
    · rcases (Nat.Prime.dvd_mul hpp).1 h1 with h2 | h2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h2))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1
          (hpp.dvd_of_dvd_pow h2)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 h1))
  have hm : p ^ (k * e) ∣ 504 := by rwa [pow_mul]
  have hlt : k * e < 9 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 9 ≤ 2 ^ (k * e) := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ (k * e) ≤ p ^ (k * e) := Nat.pow_le_pow_left hpp.two_le _
    have h3 : p ^ (k * e) ≤ 504 := Nat.le_of_dvd (by norm_num) hm
    omega
  have hkle : k ≤ k * e := Nat.le_mul_of_pos_right k he
  have hkF : p ^ k ∣ 504 := (pow_dvd_pow p hkle).trans hm
  have key : ∀ p ∈ ([2, 3, 7] : List ℕ), ∀ m < 9, p ^ m ∣ 504 → m ≤ 3 := by
    decide +kernel
  have key2 : ∀ p ∈ ([2, 3, 7] : List ℕ), ∀ m < 9, 1 ≤ m → p ^ m ∣ 504 → p ^ m ∈ q6 := by
    unfold q6
    decide +kernel
  refine ⟨key2 p h3 k (by omega) hk hkF, ?_⟩
  have := key p h3 (k * e) hlt hm
  have h8 : e ≤ k * e := Nat.le_mul_of_pos_left e hk
  omega

private theorem gen_bound504 {N G e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hG : Nat.Coprime q G) (hmul : G * N = q ^ e * R) (hN : N = 504) : q ∈ q6 ∧ e ≤ 3 := by
  have h1 : q ^ e ∣ G * 504 := ⟨R, by rw [← hN, hmul]⟩
  exact prime_power_dvd_504 hq he ((Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1)

private theorem gen_bound504' {N e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hmul : N = q ^ e * R) (hN : N = 504) : q ∈ q6 ∧ e ≤ 3 :=
  gen_bound504 hq he (Nat.coprime_one_right q) (by rw [one_mul]; exact hmul) hN

private theorem orderA_eq504 {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) (h : orderA n q = 504) :
    n = 1 ∧ q = 8 := by
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (q - 1) ∣ q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q - 1) * orderA n q =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hq6, he⟩ := gen_bound504 hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn2 : n ≤ 2 := by
    by_contra hc
    push Not at hc
    have : 6 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid1 : ∀ q ∈ q6, orderA 1 q = 504 → q = 8 := by
    unfold q6
    decide +kernel
  have grid2 : ∀ q ∈ q6, orderA 2 q ≠ 504 := by
    unfold q6
    decide +kernel
  rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
  · exact ⟨rfl, grid1 q hq6 h⟩
  · exact (grid2 q hq6 h).elim

private theorem orderTwistedA_ne504 {n q : ℕ} (hn : 2 ≤ n) (hq : IsPrimePow q) :
    orderTwistedA n q ≠ 504 := by
  intro h
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
  obtain ⟨hq6, he⟩ := gen_bound504 hq he1 (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  have hn2 : n = 2 := by
    by_contra hc
    have h3 : 3 ≤ n := by omega
    have : 6 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ q ∈ q6, orderTwistedA 2 q ≠ 504 := by
    unfold q6
    decide +kernel
  subst hn2
  exact grid q hq6 h

private theorem orderBC_ne504 {n q : ℕ} (hn : 2 ≤ n) (hq : IsPrimePow q) : orderBC n q ≠ 504 := by
  intro h
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
  obtain ⟨-, he⟩ := gen_bound504 hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  nlinarith

private theorem orderD_ne504 {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) : orderD n q ≠ 504 := by
  intro h
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
  obtain ⟨-, he⟩ := gen_bound504 hq (by omega)
    (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderTwistedD_ne504 {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) :
    orderTwistedD n q ≠ 504 := by
  intro h
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
  obtain ⟨-, he⟩ := gen_bound504 hq (by omega)
    (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderE6_ne504 {q : ℕ} (hq : IsPrimePow q) : orderE6 q ≠ 504 := by
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
  obtain ⟨-, he⟩ := gen_bound504 hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderTwistedE6_ne504 {q : ℕ} (hq : IsPrimePow q) : orderTwistedE6 q ≠ 504 := by
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
  obtain ⟨-, he⟩ := gen_bound504 hq (by norm_num)
    (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderE7_ne504 {q : ℕ} (hq : IsPrimePow q) : orderE7 q ≠ 504 := by
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
  obtain ⟨-, he⟩ := gen_bound504 hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderE8_ne504 {q : ℕ} (hq : IsPrimePow q) : orderE8 q ≠ 504 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound504' (e := 120) (R := (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) *
    (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderE8; ring) h
  omega

private theorem orderF4_ne504 {q : ℕ} (hq : IsPrimePow q) : orderF4 q ≠ 504 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound504' (e := 24) (R := (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1)) hq (by norm_num) (by unfold orderF4; ring) h
  omega

private theorem orderG2_ne504 {q : ℕ} (hq : IsPrimePow q) : orderG2 q ≠ 504 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound504' (e := 6) (R := (q ^ 6 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderG2; ring) h
  omega

private theorem orderTrialityD4_ne504 {q : ℕ} (hq : IsPrimePow q) :
    orderTrialityD4 q ≠ 504 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound504' (e := 12) (R := (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1))
    hq (by norm_num) (by unfold orderTrialityD4; ring) h
  omega

private theorem orderSuzuki_ne504 {q : ℕ} (hq : IsPrimePow q) : orderSuzuki q ≠ 504 := by
  intro h
  obtain ⟨hq6, -⟩ := gen_bound504' (e := 2) (R := (q ^ 2 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderSuzuki; ring) h
  have grid : ∀ q ∈ q6, orderSuzuki q ≠ 504 := by
    unfold q6
    decide +kernel
  exact grid q hq6 h

private theorem orderRee_ne504 {q : ℕ} (hq : IsPrimePow q) : orderRee q ≠ 504 := by
  intro h
  obtain ⟨hq6, -⟩ := gen_bound504' (e := 3) (R := (q ^ 3 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderRee; ring) h
  have grid : ∀ q ∈ q6, orderRee q ≠ 504 := by
    unfold q6
    decide +kernel
  exact grid q hq6 h

private theorem orderTwistedF4_ne504 {q : ℕ} (hq : IsPrimePow q) : orderTwistedF4 q ≠ 504 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound504' (e := 12) (R := (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1))
    hq (by norm_num) (by unfold orderTwistedF4; ring) h
  omega

private theorem orderTits_ne504 : orderTits ≠ 504 := by
  unfold orderTits
  norm_num

end OrderBounds

theorem lieOrderFormula_eq_504 {d : TauCeti.LieTypeIndex} (hd : d.Valid)
    (h : lieOrderFormula d = 504) : ∃ q : TauCeti.PrimePower, d = .A 1 q ∧ q.card = 8 := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q =>
    obtain ⟨hn1, hq8⟩ := orderA_eq504 hs.1 q.isPrimePow_card h
    subst hn1
    exact ⟨q, rfl, hq8⟩
  | twistedA n q => exact (orderTwistedA_ne504 hs.1 q.isPrimePow_card h).elim
  | B n q => exact (orderBC_ne504 hs.1 q.isPrimePow_card h).elim
  | C n q => exact (orderBC_ne504 (by have := hs.1; omega) q.isPrimePow_card h).elim
  | D n q => exact (orderD_ne504 hs q.isPrimePow_card h).elim
  | twistedD n q => exact (orderTwistedD_ne504 hs q.isPrimePow_card h).elim
  | E6 q => exact (orderE6_ne504 q.isPrimePow_card h).elim
  | E7 q => exact (orderE7_ne504 q.isPrimePow_card h).elim
  | E8 q => exact (orderE8_ne504 q.isPrimePow_card h).elim
  | F4 q => exact (orderF4_ne504 q.isPrimePow_card h).elim
  | G2 q => exact (orderG2_ne504 q.isPrimePow_card h).elim
  | twistedE6 q => exact (orderTwistedE6_ne504 q.isPrimePow_card h).elim
  | trialityD4 q => exact (orderTrialityD4_ne504 q.isPrimePow_card h).elim
  | suzuki m => exact (orderSuzuki_ne504 (Nat.prime_two.isPrimePow.pow (by omega)) h).elim
  | reeG2 m => exact (orderRee_ne504 (Nat.prime_three.isPrimePow.pow (by omega)) h).elim
  | reeF4 m => exact (orderTwistedF4_ne504 (Nat.prime_two.isPrimePow.pow (by omega)) h).elim
  | tits => exact (orderTits_ne504 h).elim

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows.Order504
