module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LieGrid

open CFSG.Open Finset CFSG.HardMathSupport.Solomon.Coordinator.I1420

@[expose] def ppDivs (ps : List ℕ) (N : ℕ) : List ℕ :=
  ((List.range 64).flatMap fun k => ps.map (· ^ (k + 1))).filter (· ∣ N)

theorem mem_ppDivs {ps : List ℕ} {N q : ℕ} (hps : ∀ p, p.Prime → p ∣ N → p ∈ ps) (hN0 : 0 < N)
    (hNlt : N < 2 ^ 64) (hq : IsPrimePow q) (hd : q ∣ N) : q ∈ ppDivs ps N := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  have hpN : p ∣ N := (dvd_pow_self p (by omega)).trans hd
  have hle : p ^ k ≤ N := Nat.le_of_dvd hN0 hd
  have hk64 : k < 65 := by
    by_contra hc
    push Not at hc
    have h1 : 2 ^ 65 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le _
    omega
  unfold ppDivs
  rw [List.mem_filter]
  refine ⟨List.mem_flatMap.2 ⟨k - 1, List.mem_range.2 (by omega), ?_⟩, by simpa using hd⟩
  rw [show k - 1 + 1 = k by omega]
  exact List.mem_map.2 ⟨p, hps p hp hpN, rfl⟩

theorem dvd_and_pow_le {M G e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (hG : Nat.Coprime q G)
    (hmul : G * M = q ^ e * R) (hM : M ≠ 0) : q ∣ M ∧ 2 ^ e ≤ M := by
  have h1 : q ^ e ∣ G * M := ⟨R, hmul⟩
  have h2 : q ^ e ∣ M := (Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1
  refine ⟨(dvd_pow_self q (by omega)).trans h2, ?_⟩
  exact (Nat.pow_le_pow_left hq.two_le e).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) h2)

theorem dvd_and_pow_le' {M e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (hmul : M = q ^ e * R)
    (hM : M ≠ 0) : q ∣ M ∧ 2 ^ e ≤ M :=
  dvd_and_pow_le hq he (Nat.coprime_one_right q) (by rw [one_mul]; exact hmul) hM

theorem orderA_mul {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) :
    q ∣ orderA n q ∧ 2 ^ (n * (n + 1) / 2) ≤ orderA n q ∨ orderA n q = 0 := by
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (q - 1) ∣ q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q - 1) * orderA n q =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  by_cases h0 : orderA n q = 0
  · exact Or.inr h0
  · exact Or.inl (dvd_and_pow_le hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
      hmul h0)

theorem orderTwistedA_mul {n q : ℕ} (hn : 2 ≤ n) (hq : IsPrimePow q) :
    q ∣ orderTwistedA n q ∧ 2 ^ (n * (n + 1) / 2) ≤ orderTwistedA n q ∨ orderTwistedA n q = 0 := by
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
  by_cases h0 : orderTwistedA n q = 0
  · exact Or.inr h0
  · exact Or.inl (dvd_and_pow_le hq he1 (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h0)

theorem orderBC_mul {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) :
    q ∣ orderBC n q ∧ 2 ^ (n * n) ≤ orderBC n q ∨ orderBC n q = 0 := by
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
  by_cases h0 : orderBC n q = 0
  · exact Or.inr h0
  · exact Or.inl (dvd_and_pow_le hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
      hmul h0)

theorem orderD_mul {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) :
    q ∣ orderD n q ∧ 2 ^ (n * (n - 1)) ≤ orderD n q ∨ orderD n q = 0 := by
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
  by_cases h0 : orderD n q = 0
  · exact Or.inr h0
  · exact Or.inl (dvd_and_pow_le hq (by omega)
      (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul h0)

theorem orderTwistedD_mul {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) :
    q ∣ orderTwistedD n q ∧ 2 ^ (n * (n - 1)) ≤ orderTwistedD n q ∨ orderTwistedD n q = 0 := by
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
  by_cases h0 : orderTwistedD n q = 0
  · exact Or.inr h0
  · exact Or.inl (dvd_and_pow_le hq (by omega)
      (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul h0)

theorem orderE6_mul {q : ℕ} (hq : IsPrimePow q) :
    q ∣ orderE6 q ∧ 2 ^ 36 ≤ orderE6 q ∨ orderE6 q = 0 := by
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
  by_cases h0 : orderE6 q = 0
  · exact Or.inr h0
  · exact Or.inl (dvd_and_pow_le hq (by norm_num)
      (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h0)

theorem orderTwistedE6_mul {q : ℕ} (hq : IsPrimePow q) :
    q ∣ orderTwistedE6 q ∧ 2 ^ 36 ≤ orderTwistedE6 q ∨ orderTwistedE6 q = 0 := by
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
  by_cases h0 : orderTwistedE6 q = 0
  · exact Or.inr h0
  · exact Or.inl (dvd_and_pow_le hq (by norm_num)
      (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h0)

theorem orderE7_mul {q : ℕ} (hq : IsPrimePow q) :
    q ∣ orderE7 q ∧ 2 ^ 63 ≤ orderE7 q ∨ orderE7 q = 0 := by
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
  by_cases h0 : orderE7 q = 0
  · exact Or.inr h0
  · exact Or.inl (dvd_and_pow_le hq (by norm_num)
      (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h0)

@[expose] def LieGridOK (ps : List ℕ) (N : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A n q => q.card ∈ ppDivs ps N ∧ n ≤ 10 ∧ orderA n q.card = N
  | .twistedA n q => q.card ∈ ppDivs ps N ∧ n ≤ 10 ∧ orderTwistedA n q.card = N
  | .B n q => q.card ∈ ppDivs ps N ∧ n ≤ 7 ∧ orderBC n q.card = N
  | .C n q => q.card ∈ ppDivs ps N ∧ n ≤ 7 ∧ orderBC n q.card = N
  | .D n q => q.card ∈ ppDivs ps N ∧ n ≤ 8 ∧ orderD n q.card = N
  | .twistedD n q => q.card ∈ ppDivs ps N ∧ n ≤ 8 ∧ orderTwistedD n q.card = N
  | .E6 q => q.card ∈ ppDivs ps N ∧ orderE6 q.card = N
  | .E7 _ => False
  | .E8 _ => False
  | .F4 q => q.card ∈ ppDivs ps N ∧ orderF4 q.card = N
  | .G2 q => q.card ∈ ppDivs ps N ∧ orderG2 q.card = N
  | .twistedE6 q => q.card ∈ ppDivs ps N ∧ orderTwistedE6 q.card = N
  | .trialityD4 q => q.card ∈ ppDivs ps N ∧ orderTrialityD4 q.card = N
  | .suzuki m => m ≤ 14 ∧ orderSuzuki (2 ^ (2 * m + 1)) = N
  | .reeG2 m => m ≤ 5 ∧ orderRee (3 ^ (2 * m + 1)) = N
  | .reeF4 m => m ≤ 1 ∧ orderTwistedF4 (2 ^ (2 * m + 1)) = N
  | .tits => orderTits = N

theorem lieGridOK_of_order {ps : List ℕ} {N : ℕ} (hps : ∀ p, p.Prime → p ∣ N → p ∈ ps)
    (hN0 : 0 < N) (hNlt : N < 2 ^ 60) {d : TauCeti.LieTypeIndex} (hs : d.InStandardRange)
    (h : lieOrderFormula d = N) : LieGridOK ps N d := by
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  have hN0' : N ≠ 0 := by omega
  have hmem : ∀ {q : ℕ}, IsPrimePow q → q ∣ N → q ∈ ppDivs ps N := fun hq hd =>
    mem_ppDivs hps hN0 (by omega) hq hd
  have hexp : ∀ {e : ℕ}, 2 ^ e ≤ N → e < 60 := fun {e} he => by
    by_contra hc
    push Not at hc
    have : 2 ^ 60 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hc
    omega
  cases d with
  | A n q =>
    simp only [lieOrderFormula] at h
    rcases orderA_mul hs.1 q.isPrimePow_card with ⟨hd, he⟩ | h0
    · rw [h] at hd he
      have h60 := hexp he
      refine ⟨hmem q.isPrimePow_card hd, ?_, h⟩
      by_contra hc
      push Not at hc
      have : 66 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
      omega
    · omega
  | twistedA n q =>
    simp only [lieOrderFormula] at h
    rcases orderTwistedA_mul hs.1 q.isPrimePow_card with ⟨hd, he⟩ | h0
    · rw [h] at hd he
      have h60 := hexp he
      refine ⟨hmem q.isPrimePow_card hd, ?_, h⟩
      by_contra hc
      push Not at hc
      have : 66 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
      omega
    · omega
  | B n q =>
    simp only [lieOrderFormula] at h
    have hn1 : 1 ≤ n := by have := hs.1; omega
    rcases orderBC_mul hn1 q.isPrimePow_card with ⟨hd, he⟩ | h0
    · rw [h] at hd he
      have h60 := hexp he
      refine ⟨hmem q.isPrimePow_card hd, ?_, h⟩
      by_contra hc
      push Not at hc
      have : 8 * 8 ≤ n * n := Nat.mul_le_mul hc hc
      omega
    · omega
  | C n q =>
    simp only [lieOrderFormula] at h
    have hn1 : 1 ≤ n := by have := hs.1; omega
    rcases orderBC_mul hn1 q.isPrimePow_card with ⟨hd, he⟩ | h0
    · rw [h] at hd he
      have h60 := hexp he
      refine ⟨hmem q.isPrimePow_card hd, ?_, h⟩
      by_contra hc
      push Not at hc
      have : 8 * 8 ≤ n * n := Nat.mul_le_mul hc hc
      omega
    · omega
  | D n q =>
    simp only [lieOrderFormula] at h
    rcases orderD_mul hs q.isPrimePow_card with ⟨hd, he⟩ | h0
    · rw [h] at hd he
      have h60 := hexp he
      refine ⟨hmem q.isPrimePow_card hd, ?_, h⟩
      by_contra hc
      push Not at hc
      have : 9 * 8 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
      omega
    · omega
  | twistedD n q =>
    simp only [lieOrderFormula] at h
    rcases orderTwistedD_mul hs q.isPrimePow_card with ⟨hd, he⟩ | h0
    · rw [h] at hd he
      have h60 := hexp he
      refine ⟨hmem q.isPrimePow_card hd, ?_, h⟩
      by_contra hc
      push Not at hc
      have : 9 * 8 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
      omega
    · omega
  | E6 q =>
    simp only [lieOrderFormula] at h
    rcases orderE6_mul q.isPrimePow_card with ⟨hd, -⟩ | h0
    · rw [h] at hd
      exact ⟨hmem q.isPrimePow_card hd, h⟩
    · omega
  | E7 q =>
    simp only [lieOrderFormula] at h
    rcases orderE7_mul q.isPrimePow_card with ⟨-, he⟩ | h0
    · rw [h] at he
      have := hexp he
      omega
    · omega
  | E8 q =>
    simp only [lieOrderFormula] at h
    obtain ⟨-, he⟩ := dvd_and_pow_le' (e := 120) (R := (q.card ^ 30 - 1) * (q.card ^ 24 - 1) *
      (q.card ^ 20 - 1) * (q.card ^ 18 - 1) * (q.card ^ 14 - 1) * (q.card ^ 12 - 1) *
      (q.card ^ 8 - 1) * (q.card ^ 2 - 1)) q.isPrimePow_card (by norm_num)
      (by unfold orderE8; ring) (h ▸ hN0')
    rw [h] at he
    have := hexp he
    omega
  | F4 q =>
    simp only [lieOrderFormula] at h
    obtain ⟨hd, -⟩ := dvd_and_pow_le' (e := 24) (R := (q.card ^ 12 - 1) * (q.card ^ 8 - 1) *
      (q.card ^ 6 - 1) * (q.card ^ 2 - 1)) q.isPrimePow_card (by norm_num)
      (by unfold orderF4; ring) (h ▸ hN0')
    rw [h] at hd
    exact ⟨hmem q.isPrimePow_card hd, h⟩
  | G2 q =>
    simp only [lieOrderFormula] at h
    obtain ⟨hd, -⟩ := dvd_and_pow_le' (e := 6) (R := (q.card ^ 6 - 1) * (q.card ^ 2 - 1))
      q.isPrimePow_card (by norm_num) (by unfold orderG2; ring) (h ▸ hN0')
    rw [h] at hd
    exact ⟨hmem q.isPrimePow_card hd, h⟩
  | twistedE6 q =>
    simp only [lieOrderFormula] at h
    rcases orderTwistedE6_mul q.isPrimePow_card with ⟨hd, -⟩ | h0
    · rw [h] at hd
      exact ⟨hmem q.isPrimePow_card hd, h⟩
    · omega
  | trialityD4 q =>
    simp only [lieOrderFormula] at h
    obtain ⟨hd, -⟩ := dvd_and_pow_le' (e := 12) (R := (q.card ^ 8 + q.card ^ 4 + 1) *
      (q.card ^ 6 - 1) * (q.card ^ 2 - 1)) q.isPrimePow_card (by norm_num)
      (by unfold orderTrialityD4; ring) (h ▸ hN0')
    rw [h] at hd
    exact ⟨hmem q.isPrimePow_card hd, h⟩
  | suzuki m =>
    simp only [lieOrderFormula] at h
    refine ⟨?_, h⟩
    by_contra hc
    push Not at hc
    have h1 : (2 ^ (2 * m + 1)) ^ 2 ∣ orderSuzuki (2 ^ (2 * m + 1)) :=
      ⟨((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1) - 1), by unfold orderSuzuki; ring⟩
    have h2 : (2 ^ (2 * m + 1)) ^ 2 ≤ N := h ▸ Nat.le_of_dvd (h ▸ hN0) h1
    have h3 : 2 ^ 60 ≤ (2 ^ (2 * m + 1)) ^ 2 := by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  | reeG2 m =>
    simp only [lieOrderFormula] at h
    refine ⟨?_, h⟩
    by_contra hc
    push Not at hc
    have h1 : (3 ^ (2 * m + 1)) ^ 3 ∣ orderRee (3 ^ (2 * m + 1)) :=
      ⟨((3 ^ (2 * m + 1)) ^ 3 + 1) * (3 ^ (2 * m + 1) - 1), by unfold orderRee; ring⟩
    have h2 : (3 ^ (2 * m + 1)) ^ 3 ≤ N := h ▸ Nat.le_of_dvd (h ▸ hN0) h1
    have h3 : 3 ^ 39 ≤ (3 ^ (2 * m + 1)) ^ 3 := by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 60 < 3 ^ 39 := by norm_num
    omega
  | reeF4 m =>
    simp only [lieOrderFormula] at h
    refine ⟨?_, h⟩
    by_contra hc
    push Not at hc
    have h1 : (2 ^ (2 * m + 1)) ^ 12 ∣ orderTwistedF4 (2 ^ (2 * m + 1)) :=
      ⟨((2 ^ (2 * m + 1)) ^ 6 + 1) * ((2 ^ (2 * m + 1)) ^ 4 - 1) * ((2 ^ (2 * m + 1)) ^ 3 + 1) *
        (2 ^ (2 * m + 1) - 1), by unfold orderTwistedF4; ring⟩
    have h2 : (2 ^ (2 * m + 1)) ^ 12 ≤ N := h ▸ Nat.le_of_dvd (h ▸ hN0) h1
    have h3 : 2 ^ 60 ≤ (2 ^ (2 * m + 1)) ^ 12 := by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  | tits => exact h

theorem hps_of_subset {N : ℕ} {ps : List ℕ} (hN : N ≠ 0) (h : N.primeFactorsList ⊆ ps) :
    ∀ p, p.Prime → p ∣ N → p ∈ ps := fun p hp hd =>
  h ((Nat.mem_primeFactorsList hN).2 ⟨hp, hd⟩)

theorem lieOrderFormula_ne_of_grid (ps : List ℕ) (N : ℕ) (hN0 : 0 < N) (hNlt : N < 2 ^ 60)
    (hps : N.primeFactorsList ⊆ ps)
    (hA : ∀ n ≤ 10, ∀ c ∈ ppDivs ps N, orderA n c ≠ N)
    (h2A : ∀ n ≤ 10, ∀ c ∈ ppDivs ps N, orderTwistedA n c ≠ N)
    (hBC : ∀ n ≤ 7, ∀ c ∈ ppDivs ps N, orderBC n c ≠ N)
    (hD : ∀ n ≤ 8, ∀ c ∈ ppDivs ps N, orderD n c ≠ N)
    (h2D : ∀ n ≤ 8, ∀ c ∈ ppDivs ps N, orderTwistedD n c ≠ N)
    (hE : ∀ c ∈ ppDivs ps N, orderE6 c ≠ N ∧ orderTwistedE6 c ≠ N ∧ orderF4 c ≠ N ∧
      orderG2 c ≠ N ∧ orderTrialityD4 c ≠ N)
    (hSz : ∀ m ≤ 14, orderSuzuki (2 ^ (2 * m + 1)) ≠ N)
    (hRee : ∀ m ≤ 5, orderRee (3 ^ (2 * m + 1)) ≠ N)
    (hRF : ∀ m ≤ 1, orderTwistedF4 (2 ^ (2 * m + 1)) ≠ N) (hT : orderTits ≠ N)
    {d : TauCeti.LieTypeIndex} (hd : d.Valid) : lieOrderFormula d ≠ N := by
  intro h
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  have hg := lieGridOK_of_order (hps_of_subset (by omega) hps) hN0 hNlt hs h
  cases d with
  | A n q => exact hA n hg.2.1 _ hg.1 hg.2.2
  | twistedA n q => exact h2A n hg.2.1 _ hg.1 hg.2.2
  | B n q => exact hBC n hg.2.1 _ hg.1 hg.2.2
  | C n q => exact hBC n hg.2.1 _ hg.1 hg.2.2
  | D n q => exact hD n hg.2.1 _ hg.1 hg.2.2
  | twistedD n q => exact h2D n hg.2.1 _ hg.1 hg.2.2
  | E6 q => exact (hE _ hg.1).1 hg.2
  | E7 q => exact hg
  | E8 q => exact hg
  | F4 q => exact (hE _ hg.1).2.2.1 hg.2
  | G2 q => exact (hE _ hg.1).2.2.2.1 hg.2
  | twistedE6 q => exact (hE _ hg.1).2.1 hg.2
  | trialityD4 q => exact (hE _ hg.1).2.2.2.2 hg.2
  | suzuki m => exact hSz m hg.1 hg.2
  | reeG2 m => exact hRee m hg.1 hg.2
  | reeF4 m => exact hRF m hg.1 hg.2
  | tits => exact hT hg

end CFSG.LocalAnalysis.GLTheoremA.LieGrid
