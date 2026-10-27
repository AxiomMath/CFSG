module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F1
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.I1420

theorem coprime_two_sub_one {x : ℕ} (hx : 2 ∣ x) (hx1 : 1 ≤ x) : Nat.Coprime 2 (x - 1) :=
  Nat.coprime_two_left.2 (Nat.odd_iff.2 (by omega))

theorem coprime_two_add_one {x : ℕ} (hx : 2 ∣ x) : Nat.Coprime 2 (x + 1) :=
  Nat.coprime_two_left.2 (Nat.odd_iff.2 (by omega))

theorem coprime_two_pow_sub_one {x n : ℕ} (hx : 2 ∣ x) (hx1 : 1 ≤ x) (hn : n ≠ 0) :
    Nat.Coprime 2 (x ^ n - 1) :=
  coprime_two_sub_one (dvd_pow hx hn) (Nat.one_le_pow _ _ (by omega))

theorem coprime_two_pow_add_one {x n : ℕ} (hx : 2 ∣ x) (hn : n ≠ 0) : Nat.Coprime 2 (x ^ n + 1) :=
  Nat.coprime_two_left.2 (Nat.odd_iff.2 (by have := dvd_pow hx hn; omega))

theorem coprime_four_of_two {g : ℕ} (h : Nat.Coprime 2 g) : Nat.Coprime 4 g := by
  simpa using Nat.Coprime.pow_left 2 h

theorem four_dvd_of_mul_eq {g m N : ℕ} (hg : Nat.Coprime 4 g) (h : g * m = N) (hN : 4 ∣ N) : 4 ∣ m :=
  hg.dvd_of_dvd_mul_left (by rw [h]; exact hN)

theorem four_dvd_pow_of_two_pow {x f e : ℕ} (hx : x = 2 ^ f) (h : 2 ≤ f * e) : 4 ∣ x ^ e := by
  subst hx
  rw [← pow_mul]
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact pow_dvd_pow 2 h

theorem two_dvd_of_two_pow {x f : ℕ} (hx : x = 2 ^ f) (hf : 1 ≤ f) : 2 ∣ x := by
  subst hx
  exact dvd_pow_self 2 (by omega)

theorem one_le_of_two_pow {x f : ℕ} (hx : x = 2 ^ f) : 1 ≤ x := by
  subst hx
  exact Nat.one_le_two_pow

theorem sub_one_dvd_sq_sub_one' (x : ℕ) : x - 1 ∣ x ^ 2 - 1 :=
  Nat.sub_one_dvd_pow_sub_one x 2

theorem add_one_dvd_sq_sub_one' {x : ℕ} (hx : 1 ≤ x) : x + 1 ∣ x ^ 2 - 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, x = r + 1 := ⟨x - 1, by omega⟩
  refine ⟨r, ?_⟩
  have : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
  omega

theorem card_eq_two_pow {q : TauCeti.PrimePower} (hq : q.p = 2) : q.card = 2 ^ q.exponent := by
  rw [TauCeti.PrimePower.card_def, hq]

theorem four_dvd_orderA {n x f : ℕ} (hn : 1 ≤ n) (hx : x = 2 ^ f) (hf : 1 ≤ f)
    (h1 : n = 1 → 4 ≤ x) : 4 ∣ orderA n x := by
  have hx2 := two_dvd_of_two_pow hx hf
  have hx1 := one_le_of_two_pow hx
  have hmem : 2 ∈ Finset.Icc 2 (n + 1) := by simp only [Finset.mem_Icc]; omega
  have hg : Nat.gcd (n + 1) (x - 1) ∣
      x ^ (n * (n + 1) / 2) * ∏ i ∈ Finset.Icc 2 (n + 1), (x ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one' x)).trans
      (Finset.dvd_prod_of_mem (fun i => x ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (x - 1) * orderA n x =
      x ^ (n * (n + 1) / 2) * ∏ i ∈ Finset.Icc 2 (n + 1), (x ^ i - 1) := Nat.mul_div_cancel' hg
  have hcop : Nat.Coprime 4 (Nat.gcd (n + 1) (x - 1)) :=
    coprime_four_of_two (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (coprime_two_sub_one hx2 hx1))
  have he : 2 ≤ f * (n * (n + 1) / 2) := by
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      have h4 := h1 rfl
      have hf2 : 2 ≤ f := by
        by_contra hc
        obtain rfl : f = 1 := by omega
        rw [pow_one] at hx
        omega
      norm_num
      omega
    · have h3 : 3 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
      have := Nat.mul_le_mul hf h3
      omega
  exact four_dvd_of_mul_eq hcop hmul (dvd_mul_of_dvd_left (four_dvd_pow_of_two_pow hx he) _)

theorem four_dvd_orderTwistedA {n x f : ℕ} (hn : 2 ≤ n) (hx : x = 2 ^ f) (hf : 1 ≤ f) :
    4 ∣ orderTwistedA n x := by
  have hx2 := two_dvd_of_two_pow hx hf
  have hx1 := one_le_of_two_pow hx
  have hmem : 2 ∈ Finset.Icc 2 (n + 1) := by simp only [Finset.mem_Icc]; omega
  have hterm : x + 1 ∣ (if Even 2 then x ^ 2 - 1 else x ^ 2 + 1) := by
    simpa using add_one_dvd_sq_sub_one' hx1
  have hg : Nat.gcd (n + 1) (x + 1) ∣ x ^ (n * (n + 1) / 2) *
      ∏ i ∈ Finset.Icc 2 (n + 1), (if Even i then x ^ i - 1 else x ^ i + 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hterm).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then x ^ i - 1 else x ^ i + 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (x + 1) * orderTwistedA n x = x ^ (n * (n + 1) / 2) *
      ∏ i ∈ Finset.Icc 2 (n + 1), (if Even i then x ^ i - 1 else x ^ i + 1) :=
    Nat.mul_div_cancel' hg
  have hcop : Nat.Coprime 4 (Nat.gcd (n + 1) (x + 1)) :=
    coprime_four_of_two (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (coprime_two_add_one hx2))
  have he : 2 ≤ f * (n * (n + 1) / 2) := by
    have h3 : 3 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    have := Nat.mul_le_mul hf h3
    omega
  exact four_dvd_of_mul_eq hcop hmul (dvd_mul_of_dvd_left (four_dvd_pow_of_two_pow hx he) _)

theorem four_dvd_orderBC {n x f : ℕ} (hn : 2 ≤ n) (hx : x = 2 ^ f) (hf : 1 ≤ f) :
    4 ∣ orderBC n x := by
  have hx2 := two_dvd_of_two_pow hx hf
  have hx1 := one_le_of_two_pow hx
  have hg : Nat.gcd 2 (x - 1) = 1 := coprime_two_sub_one hx2 hx1
  have he : 2 ≤ f * (n * n) := by
    have := Nat.mul_le_mul hf (show 4 ≤ n * n by nlinarith)
    omega
  unfold orderBC
  rw [hg, Nat.div_one]
  exact dvd_mul_of_dvd_left (four_dvd_pow_of_two_pow hx he) _

theorem four_dvd_orderD {n x f : ℕ} (hn : 4 ≤ n) (hx : x = 2 ^ f) (hf : 1 ≤ f) :
    4 ∣ orderD n x := by
  have hx2 := two_dvd_of_two_pow hx hf
  have hx1 := one_le_of_two_pow hx
  have hmul : Nat.gcd 4 (x ^ n - 1) * orderD n x =
      x ^ (n * (n - 1)) * (x ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (x ^ (2 * i) - 1) := by
    have hg : Nat.gcd 4 (x ^ n - 1) ∣
        x ^ (n * (n - 1)) * (x ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (x ^ (2 * i) - 1) :=
      Dvd.dvd.mul_right ((Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ _)) _
    exact Nat.mul_div_cancel' hg
  have hcop : Nat.Coprime 4 (Nat.gcd 4 (x ^ n - 1)) :=
    coprime_four_of_two (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (coprime_two_pow_sub_one hx2 hx1 (by omega)))
  have he : 2 ≤ f * (n * (n - 1)) := by
    have h3 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.mul_le_mul hf (show 12 ≤ n * (n - 1) by omega)
    omega
  exact four_dvd_of_mul_eq hcop hmul
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (four_dvd_pow_of_two_pow hx he) _) _)

theorem four_dvd_orderTwistedD {n x f : ℕ} (hn : 4 ≤ n) (hx : x = 2 ^ f) (hf : 1 ≤ f) :
    4 ∣ orderTwistedD n x := by
  have hx2 := two_dvd_of_two_pow hx hf
  have hmul : Nat.gcd 4 (x ^ n + 1) * orderTwistedD n x =
      x ^ (n * (n - 1)) * (x ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (x ^ (2 * i) - 1) := by
    have hg : Nat.gcd 4 (x ^ n + 1) ∣
        x ^ (n * (n - 1)) * (x ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (x ^ (2 * i) - 1) :=
      Dvd.dvd.mul_right ((Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ _)) _
    exact Nat.mul_div_cancel' hg
  have hcop : Nat.Coprime 4 (Nat.gcd 4 (x ^ n + 1)) :=
    coprime_four_of_two (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (coprime_two_pow_add_one hx2 (by omega)))
  have he : 2 ≤ f * (n * (n - 1)) := by
    have := Nat.mul_le_mul hf (show 12 ≤ n * (n - 1) by
      have h3 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega)
    omega
  exact four_dvd_of_mul_eq hcop hmul
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (four_dvd_pow_of_two_pow hx he) _) _)

theorem four_dvd_orderE6 {x f : ℕ} (hx : x = 2 ^ f) (hf : 1 ≤ f) : 4 ∣ orderE6 x := by
  have hx2 := two_dvd_of_two_pow hx hf
  have hx1 := one_le_of_two_pow hx
  have hg : Nat.gcd 3 (x - 1) ∣
      x ^ 36 * (x ^ 12 - 1) * (x ^ 9 - 1) * (x ^ 8 - 1) * (x ^ 6 - 1) * (x ^ 5 - 1) * (x ^ 2 - 1) :=
    ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one' x)).trans (dvd_mul_left _ _)
  have hmul : Nat.gcd 3 (x - 1) * orderE6 x =
      x ^ 36 * (x ^ 12 - 1) * (x ^ 9 - 1) * (x ^ 8 - 1) * (x ^ 6 - 1) * (x ^ 5 - 1) * (x ^ 2 - 1) :=
    Nat.mul_div_cancel' hg
  have hcop : Nat.Coprime 4 (Nat.gcd 3 (x - 1)) :=
    coprime_four_of_two (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (coprime_two_sub_one hx2 hx1))
  have h36 : 4 ∣ x ^ 36 := four_dvd_pow_of_two_pow hx (by omega)
  exact four_dvd_of_mul_eq hcop hmul
    ((((((h36.mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _)

theorem four_dvd_orderTwistedE6 {x f : ℕ} (hx : x = 2 ^ f) (hf : 1 ≤ f) : 4 ∣ orderTwistedE6 x := by
  have hx2 := two_dvd_of_two_pow hx hf
  have hx1 := one_le_of_two_pow hx
  have hg : Nat.gcd 3 (x + 1) ∣
      x ^ 36 * (x ^ 12 - 1) * (x ^ 9 + 1) * (x ^ 8 - 1) * (x ^ 6 - 1) * (x ^ 5 + 1) * (x ^ 2 - 1) :=
    ((Nat.gcd_dvd_right _ _).trans (add_one_dvd_sq_sub_one' hx1)).trans (dvd_mul_left _ _)
  have hmul : Nat.gcd 3 (x + 1) * orderTwistedE6 x =
      x ^ 36 * (x ^ 12 - 1) * (x ^ 9 + 1) * (x ^ 8 - 1) * (x ^ 6 - 1) * (x ^ 5 + 1) * (x ^ 2 - 1) :=
    Nat.mul_div_cancel' hg
  have hcop : Nat.Coprime 4 (Nat.gcd 3 (x + 1)) :=
    coprime_four_of_two (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (coprime_two_add_one hx2))
  have h36 : 4 ∣ x ^ 36 := four_dvd_pow_of_two_pow hx (by omega)
  exact four_dvd_of_mul_eq hcop hmul
    ((((((h36.mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _)

theorem four_dvd_orderE7 {x f : ℕ} (hx : x = 2 ^ f) (hf : 1 ≤ f) : 4 ∣ orderE7 x := by
  have hx2 := two_dvd_of_two_pow hx hf
  have hx1 := one_le_of_two_pow hx
  have hg : Nat.gcd 2 (x - 1) = 1 := coprime_two_sub_one hx2 hx1
  have h63 : 4 ∣ x ^ 63 := four_dvd_pow_of_two_pow hx (by omega)
  unfold orderE7
  rw [hg, Nat.div_one]
  exact (((((((h63.mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _)

theorem four_dvd_orderE8 {x f : ℕ} (hx : x = 2 ^ f) (hf : 1 ≤ f) : 4 ∣ orderE8 x := by
  have h120 : 4 ∣ x ^ 120 := four_dvd_pow_of_two_pow hx (by omega)
  unfold orderE8
  exact (((((((h120.mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _

theorem four_dvd_orderF4 {x f : ℕ} (hx : x = 2 ^ f) (hf : 1 ≤ f) : 4 ∣ orderF4 x := by
  have h24 : 4 ∣ x ^ 24 := four_dvd_pow_of_two_pow hx (by omega)
  unfold orderF4
  exact ((((h24.mul_right _).mul_right _).mul_right _).mul_right _)

theorem four_dvd_orderG2 {x f : ℕ} (hx : x = 2 ^ f) (hf : 1 ≤ f) : 4 ∣ orderG2 x := by
  have h6 : 4 ∣ x ^ 6 := four_dvd_pow_of_two_pow hx (by omega)
  unfold orderG2
  exact (h6.mul_right _).mul_right _

theorem four_dvd_orderTrialityD4 {x f : ℕ} (hx : x = 2 ^ f) (hf : 1 ≤ f) : 4 ∣ orderTrialityD4 x := by
  have h12 : 4 ∣ x ^ 12 := four_dvd_pow_of_two_pow hx (by omega)
  unfold orderTrialityD4
  exact (((h12.mul_right _).mul_right _).mul_right _)

theorem four_dvd_orderSuzuki {m : ℕ} (hm : 1 ≤ m) : 4 ∣ orderSuzuki (2 ^ (2 * m + 1)) := by
  have h2 : 4 ∣ (2 ^ (2 * m + 1)) ^ 2 := four_dvd_pow_of_two_pow rfl (by omega)
  unfold orderSuzuki
  exact (h2.mul_right _).mul_right _

theorem four_dvd_orderTwistedF4 {m : ℕ} (hm : 1 ≤ m) : 4 ∣ orderTwistedF4 (2 ^ (2 * m + 1)) := by
  have h12 : 4 ∣ (2 ^ (2 * m + 1)) ^ 12 := four_dvd_pow_of_two_pow rfl (by omega)
  unfold orderTwistedF4
  exact ((((h12.mul_right _).mul_right _).mul_right _).mul_right _)

theorem four_dvd_orderTits : 4 ∣ orderTits := by
  unfold orderTits
  norm_num

theorem four_dvd_lieOrderFormula {d : TauCeti.LieTypeIndex} (hv : d.Valid)
    (hc : d.characteristic = 2) : 4 ∣ lieOrderFormula d := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderA hs.1 hx q.exponent_pos hs.2
  | twistedA n q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderTwistedA hs.1 hx q.exponent_pos
  | B n q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderBC hs.1 hx q.exponent_pos
  | C n q =>
    have hq : q.p = 2 := by simpa using hc
    exact absurd hq hs.2
  | D n q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderD hs hx q.exponent_pos
  | twistedD n q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderTwistedD hs hx q.exponent_pos
  | E6 q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderE6 hx q.exponent_pos
  | E7 q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderE7 hx q.exponent_pos
  | E8 q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderE8 hx q.exponent_pos
  | F4 q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderF4 hx q.exponent_pos
  | G2 q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderG2 hx q.exponent_pos
  | twistedE6 q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderTwistedE6 hx q.exponent_pos
  | trialityD4 q =>
    have hx : q.card = 2 ^ q.exponent := card_eq_two_pow (by simpa using hc)
    exact four_dvd_orderTrialityD4 hx q.exponent_pos
  | suzuki m => exact four_dvd_orderSuzuki hs
  | reeG2 m => simp at hc
  | reeF4 m => exact four_dvd_orderTwistedF4 hs
  | tits => exact four_dvd_orderTits

theorem four_dvd_of_ambiguous_lie {d : TauCeti.LieTypeIndex} (hv : d.Valid)
    (h : ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) : 4 ∣ lieOrderFormula d := by
  cases d with
  | A n q =>
    have hn : n = 1 := by
      rcases n with _ | _ | n
      · simp [ambiguousChev] at h
      · rfl
      · simp [ambiguousChev] at h
    subst hn
    have h7 : q.card = 7 := by
      simp only [ambiguousChev] at h
      omega
    show 4 ∣ orderA 1 q.card
    rw [h7]
    decide
  | twistedA n q =>
    have hn : n = 2 := by
      rcases n with _ | _ | _ | _ | n
      · simp [ambiguousChev] at h
      · simp [ambiguousChev] at h
      · rfl
      · simp [ambiguousChev] at h
      · simp [ambiguousChev] at h
    subst hn
    have h3 : q.card = 3 := by
      simp only [ambiguousChev] at h
      omega
    show 4 ∣ orderTwistedA 2 q.card
    rw [h3]
    decide
  | B n q => simp [ambiguousChev] at h
  | C n q => simp [ambiguousChev] at h
  | D n q => simp [ambiguousChev] at h
  | twistedD n q => simp [ambiguousChev] at h
  | E6 q => simp [ambiguousChev] at h
  | E7 q => simp [ambiguousChev] at h
  | E8 q => simp [ambiguousChev] at h
  | F4 q => simp [ambiguousChev] at h
  | G2 q => simp [ambiguousChev] at h
  | twistedE6 q => simp [ambiguousChev] at h
  | trialityD4 q => simp [ambiguousChev] at h
  | suzuki m => simp [ambiguousChev] at h
  | reeG2 m => simp [ambiguousChev] at h
  | reeF4 m => simp [ambiguousChev] at h
  | tits => simp [ambiguousChev] at h

theorem not_prime_of_four_dvd {n : ℕ} (h : 4 ∣ n) (hp : n.Prime) : False := by
  have h2 : 2 ∣ n := dvd_trans (by norm_num) h
  rcases (Nat.dvd_prime hp).1 h2 with h1 | h1
  · norm_num at h1
  · rw [← h1] at h
    norm_num at h

theorem chevTwoNonabelian_holds :
    ChevTwoNonabelian := by
  intro S _ _ hS hchev
  by_contra hcomm
  push Not at hcomm
  haveI : IsMulCommutative S := ⟨⟨fun a b => hcomm a b⟩⟩
  have hprime : (Nat.card S).Prime := Group.is_simple_iff_prime_card.1 hS
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      have hcard : Nat.card S = lieOrderFormula d := lieOrderBridge_holds ⟨d, hv⟩ S ⟨e⟩
      have h4 : 4 ∣ lieOrderFormula d := four_dvd_lieOrderFormula hv hi
      rw [← hcard] at h4
      exact not_prime_of_four_dvd h4 hprime
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating n hn5 =>
      have hn : n = 5 ∨ n = 6 ∨ n = 8 := by
        simp only [ambiguousChev] at hi
        omega
      rcases hn with rfl | rfl | rfl
      · have hc : Nat.card S = 60 := by
          rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
          simp [Nat.factorial]
        exact not_prime_of_four_dvd (by rw [hc]; norm_num) hprime
      · have hc : Nat.card S = 360 := by
          rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
          simp [Nat.factorial]
        exact not_prime_of_four_dvd (by rw [hc]; norm_num) hprime
      · have hc : Nat.card S = 20160 := by
          rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
          simp [Nat.factorial]
        exact not_prime_of_four_dvd (by rw [hc]; norm_num) hprime
    | sporadic _ => exact hi.elim
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      have h4 : 4 ∣ lieOrderFormula d := four_dvd_of_ambiguous_lie hv hi
      have hcard : Nat.card S = lieOrderFormula d := lieOrderBridge_holds ⟨d, hv⟩ S ⟨e⟩
      rw [← hcard] at h4
      exact not_prime_of_four_dvd h4 hprime

end CFSG.LocalAnalysis.GLTheoremA

end
