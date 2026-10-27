module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows.Order181440

open CFSG.HardMathSupport.Solomon.Coordinator.I1420

section OrderBounds

open CFSG.Open Finset

private def q6 : List ℕ := [2, 4, 8, 16, 32, 64, 3, 9, 27, 81, 5, 7]

private theorem prime_power_dvd_181440 {q e : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (h : q ^ e ∣ 181440) : q ∈ q6 ∧ e ≤ 6 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  have hpp : p.Prime := hp
  have hpF : p ∣ 181440 :=
    (dvd_pow_self p (by omega : k ≠ 0)).trans ((dvd_pow_self (p ^ k) (by omega : e ≠ 0)).trans h)
  have h3 : p ∈ ([2, 3, 5, 7] : List ℕ) := by
    have hN : (181440 : ℕ) = 2 ^ 6 * 3 ^ 4 * 5 * 7 := by norm_num
    rw [hN] at hpF
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases (Nat.Prime.dvd_mul hpp).1 hpF with h1 | h1
    · rcases (Nat.Prime.dvd_mul hpp).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hpp).1 h2 with h4 | h4
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h4))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1
            (hpp.dvd_of_dvd_pow h4)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).1 h2)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 h1)))
  have hm : p ^ (k * e) ∣ 181440 := by rwa [pow_mul]
  have hlt : k * e < 18 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 18 ≤ 2 ^ (k * e) := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ (k * e) ≤ p ^ (k * e) := Nat.pow_le_pow_left hpp.two_le _
    have h3 : p ^ (k * e) ≤ 181440 := Nat.le_of_dvd (by norm_num) hm
    omega
  have hkle : k ≤ k * e := Nat.le_mul_of_pos_right k he
  have hkF : p ^ k ∣ 181440 := (pow_dvd_pow p hkle).trans hm
  have key : ∀ p ∈ ([2, 3, 5, 7] : List ℕ), ∀ m < 18, p ^ m ∣ 181440 → m ≤ 6 := by
    decide +kernel
  have key2 : ∀ p ∈ ([2, 3, 5, 7] : List ℕ), ∀ m < 18, 1 ≤ m → p ^ m ∣ 181440 → p ^ m ∈ q6 := by
    unfold q6
    decide +kernel
  refine ⟨key2 p h3 k (by omega) hk hkF, ?_⟩
  have := key p h3 (k * e) hlt hm
  have h8 : e ≤ k * e := Nat.le_mul_of_pos_left e hk
  omega

private theorem gen_bound181440 {N G e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hG : Nat.Coprime q G) (hmul : G * N = q ^ e * R) (hN : N = 181440) : q ∈ q6 ∧ e ≤ 6 := by
  have h1 : q ^ e ∣ G * 181440 := ⟨R, by rw [← hN, hmul]⟩
  exact prime_power_dvd_181440 hq he ((Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1)

private theorem gen_bound181440' {N e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hmul : N = q ^ e * R) (hN : N = 181440) : q ∈ q6 ∧ e ≤ 6 :=
  gen_bound181440 hq he (Nat.coprime_one_right q) (by rw [one_mul]; exact hmul) hN

private theorem orderA_ne181440 {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) (h9 : n = 1 → q ≠ 9) :
    orderA n q ≠ 181440 := by
  intro h
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (q - 1) ∣ q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q - 1) * orderA n q =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hq6, he⟩ := gen_bound181440 hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn3 : n ≤ 3 := by
    by_contra hc
    push Not at hc
    have : 10 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid1 : ∀ q ∈ q6, q ≠ 9 → orderA 1 q ≠ 181440 := by
    unfold q6
    decide +kernel
  have grid2 : ∀ q ∈ q6, orderA 2 q ≠ 181440 := by
    unfold q6
    decide +kernel
  have grid3 : ∀ q ∈ q6, orderA 3 q ≠ 181440 := by
    unfold q6
    decide +kernel
  rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl
  · exact grid1 q hq6 (h9 rfl) h
  · exact grid2 q hq6 h
  · exact grid3 q hq6 h

private theorem orderTwistedA_ne181440 {n q : ℕ} (hn : 2 ≤ n) (hq : IsPrimePow q) :
    orderTwistedA n q ≠ 181440 := by
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
  obtain ⟨hq6, he⟩ := gen_bound181440 hq he1 (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  have hn3 : n ≤ 3 := by
    by_contra hc
    push Not at hc
    have : 10 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid2 : ∀ q ∈ q6, orderTwistedA 2 q ≠ 181440 := by
    unfold q6
    decide +kernel
  have grid3 : ∀ q ∈ q6, orderTwistedA 3 q ≠ 181440 := by
    unfold q6
    decide +kernel
  rcases (by omega : n = 2 ∨ n = 3) with rfl | rfl
  · exact grid2 q hq6 h
  · exact grid3 q hq6 h

private theorem orderBC_ne181440 {n q : ℕ} (hn : 2 ≤ n) (hq : IsPrimePow q) : orderBC n q ≠ 181440 := by
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
  obtain ⟨hq6, he⟩ := gen_bound181440 hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn2 : n = 2 := by nlinarith
  have grid : ∀ q ∈ q6, orderBC 2 q ≠ 181440 := by
    unfold q6
    decide +kernel
  subst hn2
  exact grid q hq6 h

private theorem orderD_ne181440 {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) : orderD n q ≠ 181440 := by
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
  obtain ⟨-, he⟩ := gen_bound181440 hq (by omega)
    (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderTwistedD_ne181440 {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) :
    orderTwistedD n q ≠ 181440 := by
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
  obtain ⟨-, he⟩ := gen_bound181440 hq (by omega)
    (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderE6_ne181440 {q : ℕ} (hq : IsPrimePow q) : orderE6 q ≠ 181440 := by
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
  obtain ⟨-, he⟩ := gen_bound181440 hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderTwistedE6_ne181440 {q : ℕ} (hq : IsPrimePow q) : orderTwistedE6 q ≠ 181440 := by
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
  obtain ⟨-, he⟩ := gen_bound181440 hq (by norm_num)
    (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderE7_ne181440 {q : ℕ} (hq : IsPrimePow q) : orderE7 q ≠ 181440 := by
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
  obtain ⟨-, he⟩ := gen_bound181440 hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  omega

private theorem orderE8_ne181440 {q : ℕ} (hq : IsPrimePow q) : orderE8 q ≠ 181440 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound181440' (e := 120) (R := (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) *
    (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderE8; ring) h
  omega

private theorem orderF4_ne181440 {q : ℕ} (hq : IsPrimePow q) : orderF4 q ≠ 181440 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound181440' (e := 24) (R := (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1)) hq (by norm_num) (by unfold orderF4; ring) h
  omega

private theorem orderG2_ne181440 {q : ℕ} (hq : IsPrimePow q) : orderG2 q ≠ 181440 := by
  intro h
  obtain ⟨hq6, -⟩ := gen_bound181440' (e := 6) (R := (q ^ 6 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderG2; ring) h
  have grid : ∀ q ∈ q6, orderG2 q ≠ 181440 := by
    unfold q6
    decide +kernel
  exact grid q hq6 h

private theorem orderTrialityD4_ne181440 {q : ℕ} (hq : IsPrimePow q) :
    orderTrialityD4 q ≠ 181440 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound181440' (e := 12) (R := (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1))
    hq (by norm_num) (by unfold orderTrialityD4; ring) h
  omega

private theorem orderSuzuki_ne181440 {q : ℕ} (hq : IsPrimePow q) : orderSuzuki q ≠ 181440 := by
  intro h
  obtain ⟨hq6, -⟩ := gen_bound181440' (e := 2) (R := (q ^ 2 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderSuzuki; ring) h
  have grid : ∀ q ∈ q6, orderSuzuki q ≠ 181440 := by
    unfold q6
    decide +kernel
  exact grid q hq6 h

private theorem orderRee_ne181440 {q : ℕ} (hq : IsPrimePow q) : orderRee q ≠ 181440 := by
  intro h
  obtain ⟨hq6, -⟩ := gen_bound181440' (e := 3) (R := (q ^ 3 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderRee; ring) h
  have grid : ∀ q ∈ q6, orderRee q ≠ 181440 := by
    unfold q6
    decide +kernel
  exact grid q hq6 h

private theorem orderTwistedF4_ne181440 {q : ℕ} (hq : IsPrimePow q) : orderTwistedF4 q ≠ 181440 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound181440' (e := 12) (R := (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1))
    hq (by norm_num) (by unfold orderTwistedF4; ring) h
  omega

private theorem orderTits_ne181440 : orderTits ≠ 181440 := by
  unfold orderTits
  norm_num

end OrderBounds

theorem lieOrderFormula_ne_181440 {d : TauCeti.LieTypeIndex} (hd : d.Valid) :
    lieOrderFormula d ≠ 181440 := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  have hdup : ¬ d.IsDuplicateRepresentative := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).2
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  cases d with
  | A n q =>
    exact orderA_ne181440 hs.1 q.isPrimePow_card
      (fun hn h9 => hdup (Or.inl ⟨hn, Or.inr (Or.inr h9)⟩))
  | twistedA n q => exact orderTwistedA_ne181440 hs.1 q.isPrimePow_card
  | B n q => exact orderBC_ne181440 hs.1 q.isPrimePow_card
  | C n q => exact orderBC_ne181440 (by have := hs.1; omega) q.isPrimePow_card
  | D n q => exact orderD_ne181440 hs q.isPrimePow_card
  | twistedD n q => exact orderTwistedD_ne181440 hs q.isPrimePow_card
  | E6 q => exact orderE6_ne181440 q.isPrimePow_card
  | E7 q => exact orderE7_ne181440 q.isPrimePow_card
  | E8 q => exact orderE8_ne181440 q.isPrimePow_card
  | F4 q => exact orderF4_ne181440 q.isPrimePow_card
  | G2 q => exact orderG2_ne181440 q.isPrimePow_card
  | twistedE6 q => exact orderTwistedE6_ne181440 q.isPrimePow_card
  | trialityD4 q => exact orderTrialityD4_ne181440 q.isPrimePow_card
  | suzuki m => exact orderSuzuki_ne181440 (Nat.prime_two.isPrimePow.pow (by omega))
  | reeG2 m => exact orderRee_ne181440 (Nat.prime_three.isPrimePow.pow (by omega))
  | reeF4 m => exact orderTwistedF4_ne181440 (Nat.prime_two.isPrimePow.pow (by omega))
  | tits => exact orderTits_ne181440

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows.Order181440
