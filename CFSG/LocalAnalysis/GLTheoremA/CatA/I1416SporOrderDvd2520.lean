module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows.OrderDvd2520

open CFSG.HardMathSupport.Solomon.Coordinator.I1420

@[expose] def ords : List ℕ := [6, 12, 20, 60, 72, 168, 360, 504]

section OrderBounds

open CFSG.Open Finset

private def q7 : List ℕ := [2, 4, 8, 3, 9, 5, 7]

private theorem prime_power_dvd_2520 {q e : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (h : q ^ e ∣ 2520) : q ∈ q7 ∧ e ≤ 3 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  have hpp : p.Prime := hp
  have hpF : p ∣ 2520 :=
    (dvd_pow_self p (by omega : k ≠ 0)).trans ((dvd_pow_self (p ^ k) (by omega : e ≠ 0)).trans h)
  have h3 : p ∈ ([2, 3, 5, 7] : List ℕ) := by
    have h2520 : (2520 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by norm_num
    rw [h2520] at hpF
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases (Nat.Prime.dvd_mul hpp).1 hpF with h1 | h1
    · rcases (Nat.Prime.dvd_mul hpp).1 h1 with h1 | h1
      · rcases (Nat.Prime.dvd_mul hpp).1 h1 with h2 | h2
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h2))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1
            (hpp.dvd_of_dvd_pow h2)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).1 h1)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 h1)))
  have hm : p ^ (k * e) ∣ 2520 := by rwa [pow_mul]
  have hlt : k * e < 12 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 12 ≤ 2 ^ (k * e) := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ (k * e) ≤ p ^ (k * e) := Nat.pow_le_pow_left hpp.two_le _
    have h3 : p ^ (k * e) ≤ 2520 := Nat.le_of_dvd (by norm_num) hm
    omega
  have hkle : k ≤ k * e := Nat.le_mul_of_pos_right k he
  have hkF : p ^ k ∣ 2520 := (pow_dvd_pow p hkle).trans hm
  have key : ∀ p ∈ ([2, 3, 5, 7] : List ℕ), ∀ m < 12, p ^ m ∣ 2520 → m ≤ 3 := by
    decide +kernel
  have key2 : ∀ p ∈ ([2, 3, 5, 7] : List ℕ), ∀ m < 12, 1 ≤ m → p ^ m ∣ 2520 → p ^ m ∈ q7 := by
    unfold q7
    decide +kernel
  refine ⟨key2 p h3 k (by omega) hk hkF, ?_⟩
  have := key p h3 (k * e) hlt hm
  have h8 : e ≤ k * e := Nat.le_mul_of_pos_left e hk
  omega

private theorem gen_bound {N G e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hG : Nat.Coprime q G) (hmul : G * N = q ^ e * R) (hN : N ∣ 2520) : q ∈ q7 ∧ e ≤ 3 := by
  have h1 : q ^ e ∣ G * 2520 := (Dvd.intro R hmul.symm).trans (mul_dvd_mul_left G hN)
  exact prime_power_dvd_2520 hq he ((Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1)

private theorem gen_bound' {N e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hmul : N = q ^ e * R) (hN : N ∣ 2520) : q ∈ q7 ∧ e ≤ 3 :=
  gen_bound hq he (Nat.coprime_one_right q) (by rw [one_mul]; exact hmul) hN

private theorem orderA_dvd {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) (h : orderA n q ∣ 2520) :
    orderA n q ∈ ords := by
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
  have hn2 : n ≤ 2 := by
    by_contra hc
    push Not at hc
    have : 6 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid1 : ∀ q ∈ q7, orderA 1 q ∣ 2520 → orderA 1 q ∈ ords := by
    unfold q7 ords
    decide +kernel
  have grid2 : ∀ q ∈ q7, orderA 2 q ∣ 2520 → orderA 2 q ∈ ords := by
    unfold q7 ords
    decide +kernel
  rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
  · exact grid1 q hq5 h
  · exact grid2 q hq5 h

private theorem orderTwistedA_dvd {n q : ℕ} (hn : 2 ≤ n) (hq : IsPrimePow q)
    (h : orderTwistedA n q ∣ 2520) : orderTwistedA n q ∈ ords := by
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
  have hn2 : n = 2 := by
    by_contra hc
    have h3 : 3 ≤ n := by omega
    have : 6 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ q ∈ q7, orderTwistedA 2 q ∣ 2520 → orderTwistedA 2 q ∈ ords := by
    unfold q7 ords
    decide +kernel
  subst hn2
  exact grid q hq5 h

private theorem orderBC_dvd {n q : ℕ} (hn : 2 ≤ n) (hq : IsPrimePow q) :
    ¬ orderBC n q ∣ 2520 := by
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
  obtain ⟨-, he⟩ := gen_bound hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  nlinarith

private theorem orderD_dvd {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) : ¬ orderD n q ∣ 2520 := by
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
  obtain ⟨-, he⟩ := gen_bound hq (by omega)
    (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderTwistedD_dvd {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) :
    ¬ orderTwistedD n q ∣ 2520 := by
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
  obtain ⟨-, he⟩ := gen_bound hq (by omega)
    (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderE6_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderE6 q ∣ 2520 := by
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

private theorem orderTwistedE6_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderTwistedE6 q ∣ 2520 := by
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

private theorem orderE7_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderE7 q ∣ 2520 := by
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

private theorem orderE8_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderE8 q ∣ 2520 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 120) (R := (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) *
    (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderE8; ring) h
  omega

private theorem orderF4_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderF4 q ∣ 2520 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 24) (R := (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1)) hq (by norm_num) (by unfold orderF4; ring) h
  omega

private theorem orderG2_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderG2 q ∣ 2520 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 6) (R := (q ^ 6 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderG2; ring) h
  omega

private theorem orderTrialityD4_dvd {q : ℕ} (hq : IsPrimePow q) :
    ¬ orderTrialityD4 q ∣ 2520 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 12) (R := (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1))
    hq (by norm_num) (by unfold orderTrialityD4; ring) h
  omega

private theorem orderSuzuki_dvd {m : ℕ} (h : orderSuzuki (2 ^ (2 * m + 1)) ∣ 2520) :
    orderSuzuki (2 ^ (2 * m + 1)) ∈ ords := by
  obtain ⟨hq5, -⟩ := gen_bound' (q := 2 ^ (2 * m + 1)) (e := 2)
    (R := ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1) - 1))
    (Nat.prime_two.isPrimePow.pow (by omega)) (by norm_num) (by unfold orderSuzuki; ring) h
  have hle : 2 ^ (2 * m + 1) ≤ 9 := by
    unfold q7 at hq5
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq5
    omega
  have hm : m = 0 ∨ m = 1 := by
    by_contra hc
    have : 2 ^ 5 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases hm with rfl | rfl
  · unfold ords; decide
  · exfalso; revert h; decide

private theorem orderRee_dvd {m : ℕ} : ¬ orderRee (3 ^ (2 * m + 1)) ∣ 2520 := by
  intro h
  obtain ⟨hq5, -⟩ := gen_bound' (q := 3 ^ (2 * m + 1)) (e := 3)
    (R := ((3 ^ (2 * m + 1)) ^ 3 + 1) * (3 ^ (2 * m + 1) - 1))
    (Nat.prime_three.isPrimePow.pow (by omega)) (by norm_num) (by unfold orderRee; ring) h
  have hle : 3 ^ (2 * m + 1) ≤ 9 := by
    unfold q7 at hq5
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq5
    omega
  have hm : m = 0 := by
    by_contra hc
    have : 3 ^ 3 ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hm
  revert h
  decide

private theorem orderTwistedF4_dvd {q : ℕ} (hq : IsPrimePow q) : ¬ orderTwistedF4 q ∣ 2520 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 12) (R := (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1))
    hq (by norm_num) (by unfold orderTwistedF4; ring) h
  omega

private theorem orderTits_dvd : ¬ orderTits ∣ 2520 := by
  unfold orderTits
  norm_num

end OrderBounds

theorem lieOrderFormula_dvd_2520 {d : TauCeti.LieTypeIndex} (hd : d.Valid)
    (h : lieOrderFormula d ∣ 2520) : lieOrderFormula d ∈ ords := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q => exact orderA_dvd hs.1 q.isPrimePow_card h
  | twistedA n q => exact orderTwistedA_dvd hs.1 q.isPrimePow_card h
  | B n q => exact absurd h (orderBC_dvd hs.1 q.isPrimePow_card)
  | C n q => exact absurd h (orderBC_dvd (by have := hs.1; omega) q.isPrimePow_card)
  | D n q => exact absurd h (orderD_dvd hs q.isPrimePow_card)
  | twistedD n q => exact absurd h (orderTwistedD_dvd hs q.isPrimePow_card)
  | E6 q => exact absurd h (orderE6_dvd q.isPrimePow_card)
  | E7 q => exact absurd h (orderE7_dvd q.isPrimePow_card)
  | E8 q => exact absurd h (orderE8_dvd q.isPrimePow_card)
  | F4 q => exact absurd h (orderF4_dvd q.isPrimePow_card)
  | G2 q => exact absurd h (orderG2_dvd q.isPrimePow_card)
  | twistedE6 q => exact absurd h (orderTwistedE6_dvd q.isPrimePow_card)
  | trialityD4 q => exact absurd h (orderTrialityD4_dvd q.isPrimePow_card)
  | suzuki m => exact orderSuzuki_dvd h
  | reeG2 m => exact absurd h orderRee_dvd
  | reeF4 m => exact absurd h (orderTwistedF4_dvd (Nat.prime_two.isPrimePow.pow (by omega)))
  | tits => exact absurd h orderTits_dvd

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows.OrderDvd2520
