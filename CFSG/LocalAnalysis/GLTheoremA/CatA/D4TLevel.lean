module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4T

open CFSG.Open Finset
open CFSG.HardMathSupport.Solomon.Coordinator.I1420

@[expose] def N8 : ℕ := 174182400

theorem two_pow_pow_le {f e : ℕ} (h : (2 ^ f) ^ e ∣ N8) : f * e ≤ 12 := by
  by_contra hc
  push Not at hc
  have h1 : 2 ^ 13 ∣ (2 ^ f) ^ e := by
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  have h2 : 2 ^ 13 ∣ N8 := h1.trans h
  revert h2
  unfold N8
  decide +kernel

theorem pow_dvd_div {q e R g : ℕ} (hg : Nat.Coprime q g) (hgd : g ∣ q ^ e * R) :
    q ^ e ∣ q ^ e * R / g := by
  have hmul : g * (q ^ e * R / g) = q ^ e * R := Nat.mul_div_cancel' hgd
  have h1 : q ^ e ∣ g * (q ^ e * R / g) := ⟨R, hmul⟩
  exact (Nat.Coprime.pow_left e hg).dvd_of_dvd_mul_left h1

theorem two_le_two_pow {f : ℕ} (hf : 1 ≤ f) : 2 ≤ 2 ^ f := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem card_two_pow {q : TauCeti.PrimePower} (hp : q.p = 2) : q.card = 2 ^ q.exponent := by
  rw [TauCeti.PrimePower.card_def, hp]

theorem tri_bounds {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hb : f * (n * (n + 1) / 2) ≤ 12) :
    n ≤ 4 ∧ f ≤ 12 := by
  constructor
  · by_contra hc
    push Not at hc
    have : 15 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    nlinarith
  · have : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
    nlinarith

theorem d4_small {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hb : f * (n * (n - 1)) ≤ 12) :
    n = 4 ∧ f = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e : m + 4 - 1 = m + 3 := by omega
  rw [e] at hb
  have hle : (m + 4) * (m + 3) ≤ f * ((m + 4) * (m + 3)) := Nat.le_mul_of_pos_left _ hf
  have hm : m = 0 := by nlinarith
  have hf1 : f = 1 := by subst hm; nlinarith
  exact ⟨by omega, hf1⟩

theorem orderA_pow_dvd {n q : ℕ} (hn : 1 ≤ n) (hq2 : 2 ≤ q) :
    q ^ (n * (n + 1) / 2) ∣ orderA n q := by
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (q - 1) ∣ q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem)) _
  exact pow_dvd_div (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hGd

theorem orderTwistedA_pow_dvd {n q : ℕ} (hn : 1 ≤ n) (hq2 : 2 ≤ q) :
    q ^ (n * (n + 1) / 2) ∣ orderTwistedA n q := by
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hfac : q + 1 ∣ (fun i => if Even i then q ^ i - 1 else q ^ i + 1) 2 := by
    show q + 1 ∣ (if Even 2 then q ^ 2 - 1 else q ^ 2 + 1)
    simpa using add_one_dvd_sq_sub_one q (by omega)
  have hGd : Nat.gcd (n + 1) (q + 1) ∣ q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hmem)) _
  exact pow_dvd_div (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hGd

theorem orderBC_pow_dvd {n q : ℕ} (hn : 1 ≤ n) (hq2 : 2 ≤ q) : q ^ (n * n) ∣ orderBC n q := by
  have hmem : 1 ∈ Icc 1 n := by simp; omega
  have hfac : q - 1 ∣ (fun i => q ^ (2 * i) - 1) 1 := by
    show q - 1 ∣ q ^ (2 * 1) - 1
    exact Nat.sub_one_dvd_pow_sub_one q (2 * 1)
  have hGd : Nat.gcd 2 (q - 1) ∣ q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem)) _
  exact pow_dvd_div (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hGd

theorem orderD_pow_dvd {n q : ℕ} (hn : 1 ≤ n) (hq2 : 2 ≤ q) :
    q ^ (n * (n - 1)) ∣ orderD n q := by
  unfold orderD
  rw [mul_assoc (q ^ (n * (n - 1)))]
  refine pow_dvd_div (coprime_of_dvd_pow_sub_one hq2 hn (Nat.gcd_dvd_right _ _)) ?_
  exact Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)) _

theorem orderTwistedD_pow_dvd {n q : ℕ} (hn : 1 ≤ n) :
    q ^ (n * (n - 1)) ∣ orderTwistedD n q := by
  unfold orderTwistedD
  rw [mul_assoc (q ^ (n * (n - 1)))]
  refine pow_dvd_div (coprime_of_dvd_pow_add_one hn (Nat.gcd_dvd_right _ _)) ?_
  exact Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)) _

theorem orderG2_pow_dvd (q : ℕ) : q ^ 6 ∣ orderG2 q := by
  unfold orderG2; simp only [mul_assoc]; exact dvd_mul_right _ _

theorem orderTrialityD4_pow_dvd (q : ℕ) : q ^ 12 ∣ orderTrialityD4 q := by
  unfold orderTrialityD4; simp only [mul_assoc]; exact dvd_mul_right _ _

theorem orderSuzuki_pow_dvd (q : ℕ) : q ^ 2 ∣ orderSuzuki q := by
  unfold orderSuzuki; simp only [mul_assoc]; exact dvd_mul_right _ _

theorem orderF4_pow_dvd (q : ℕ) : q ^ 24 ∣ orderF4 q := by
  unfold orderF4; simp only [mul_assoc]; exact dvd_mul_right _ _

theorem orderTwistedF4_pow_dvd (q : ℕ) : q ^ 12 ∣ orderTwistedF4 q := by
  unfold orderTwistedF4; simp only [mul_assoc]; exact dvd_mul_right _ _

theorem orderE6_pow_dvd {q : ℕ} (hq2 : 2 ≤ q) : q ^ 36 ∣ orderE6 q := by
  unfold orderE6
  simp only [mul_assoc]
  refine pow_dvd_div (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) ?_
  exact Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
    ((((((dvd_refl _).mul_left _).mul_left _).mul_left _).mul_left _).mul_left _)) _

theorem orderTwistedE6_pow_dvd {q : ℕ} (hq2 : 2 ≤ q) : q ^ 36 ∣ orderTwistedE6 q := by
  unfold orderTwistedE6
  simp only [mul_assoc]
  refine pow_dvd_div (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) ?_
  exact Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (add_one_dvd_sq_sub_one q (by omega))).trans
    ((((((dvd_refl _).mul_left _).mul_left _).mul_left _).mul_left _).mul_left _)) _

theorem orderE7_pow_dvd {q : ℕ} (hq2 : 2 ≤ q) : q ^ 63 ∣ orderE7 q := by
  unfold orderE7
  simp only [mul_assoc]
  refine pow_dvd_div (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) ?_
  exact Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
    (((((((dvd_refl _).mul_left _).mul_left _).mul_left _).mul_left _).mul_left _).mul_left _)) _

theorem orderE8_pow_dvd (q : ℕ) : q ^ 120 ∣ orderE8 q := by
  unfold orderE8; simp only [mul_assoc]; exact dvd_mul_right _ _

theorem gridA : ∀ n ∈ ([1, 2, 3, 4] : List ℕ),
    ∀ f ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List ℕ), orderA n (2 ^ f) ∣ N8 →
      (n = 1 ∧ (f = 1 ∨ f = 2 ∨ f = 3)) ∨ (n = 2 ∧ (f = 1 ∨ f = 2)) ∨ (n = 3 ∧ f = 1) := by
  unfold N8
  decide +kernel

theorem gridTA : ∀ n ∈ ([2, 3, 4] : List ℕ),
    ∀ f ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List ℕ), orderTwistedA n (2 ^ f) ∣ N8 →
      (n = 2 ∧ f = 1) ∨ (n = 3 ∧ f = 1) := by
  unfold N8
  decide +kernel

theorem gridBC : ∀ n ∈ ([2, 3] : List ℕ),
    ∀ f ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List ℕ), orderBC n (2 ^ f) ∣ N8 →
      (n = 2 ∧ f = 1) ∨ (n = 3 ∧ f = 1) := by
  unfold N8
  decide +kernel

theorem gridG2 : ∀ f ∈ ([1, 2] : List ℕ), orderG2 (2 ^ f) ∣ N8 → f = 1 := by
  unfold N8
  decide +kernel

theorem gridSz : ∀ m ∈ ([1, 2] : List ℕ), ¬ orderSuzuki (2 ^ (2 * m + 1)) ∣ N8 := by
  unfold N8
  decide +kernel

theorem orderA_cases {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) (h : orderA n (2 ^ f) ∣ N8) :
    (n = 1 ∧ (f = 1 ∨ f = 2 ∨ f = 3)) ∨ (n = 2 ∧ (f = 1 ∨ f = 2)) ∨ (n = 3 ∧ f = 1) := by
  obtain ⟨hn4, hf12⟩ := tri_bounds hn hf
    (two_pow_pow_le ((orderA_pow_dvd hn (two_le_two_pow hf)).trans h))
  exact gridA n (by simp; omega) f (by simp; omega) h

theorem orderTwistedA_cases {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    (h : orderTwistedA n (2 ^ f) ∣ N8) : (n = 2 ∧ f = 1) ∨ (n = 3 ∧ f = 1) := by
  obtain ⟨hn4, hf12⟩ := tri_bounds (by omega) hf
    (two_pow_pow_le ((orderTwistedA_pow_dvd (by omega) (two_le_two_pow hf)).trans h))
  exact gridTA n (by simp; omega) f (by simp; omega) h

theorem orderBC_cases {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) (h : orderBC n (2 ^ f) ∣ N8) :
    (n = 2 ∧ f = 1) ∨ (n = 3 ∧ f = 1) := by
  have hb := two_pow_pow_le ((orderBC_pow_dvd (by omega) (two_le_two_pow hf)).trans h)
  have hn3 : n ≤ 3 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hf12 : f ≤ 12 := by nlinarith
  exact gridBC n (by simp; omega) f (by simp; omega) h

theorem orderD_cases {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (h : orderD n (2 ^ f) ∣ N8) :
    n = 4 ∧ f = 1 :=
  d4_small hn hf (two_pow_pow_le ((orderD_pow_dvd (by omega) (two_le_two_pow hf)).trans h))

theorem orderTwistedD_false {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (h : orderTwistedD n (2 ^ f) ∣ N8) :
    False := by
  obtain ⟨rfl, rfl⟩ := d4_small hn hf
    (two_pow_pow_le ((orderTwistedD_pow_dvd (q := 2 ^ f) (by omega)).trans h))
  revert h
  unfold N8
  decide +kernel

open CFSG.Yardstones.Md0ec50421ce4 in
theorem chev2_index_good (d : TauCeti.LieTypeIndex) (hv : d.Valid) (hch : d.characteristic = 2)
    (hdvd : lieOrderFormula d ∣ N8) :
    k2Lie 3 d ∨ ∃ q, d = .twistedA 3 q ∧ q.card = 2 := by
  simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hv
  obtain ⟨hr, hdup⟩ := hv
  cases d with
  | A n q =>
    have hp : q.p = 2 := by simpa using hch
    have hcard := card_two_pow hp
    have hdvd' : orderA n (2 ^ q.exponent) ∣ N8 := by rw [← hcard]; exact hdvd
    obtain ⟨hn1, hq4⟩ := hr
    rcases orderA_cases hn1 q.exponent_pos hdvd' with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩
    · rcases hf with hf | hf | hf
      · exfalso
        have := hq4 rfl
        rw [hcard, hf] at this
        norm_num at this
      · exfalso
        apply hdup
        left
        exact ⟨rfl, Or.inl (by rw [hcard, hf]; norm_num)⟩
      · left
        show 3 = 3 ∧ ¬ 3 ∣ q.card
        rw [hcard, hf]
        norm_num
    · rcases hf with hf | hf
      · exfalso
        apply hdup
        right; left
        exact ⟨rfl, by rw [hcard, hf]; norm_num⟩
      · left
        show (3 = 3 ∧ q.p = 2 ∧ Even q.exponent) ∨ (3 = 13 ∧ q.card = 3)
        left
        exact ⟨rfl, hp, by rw [hf]; decide⟩
    · exfalso
      apply hdup
      right; right
      exact ⟨rfl, by rw [hcard, hf]; norm_num⟩
  | twistedA n q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hdvd' : orderTwistedA n (2 ^ q.exponent) ∣ N8 := by rw [← hcard]; exact hdvd
    obtain ⟨hn2, hq3⟩ := hr
    rcases orderTwistedA_cases hn2 q.exponent_pos hdvd' with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
    · exfalso
      have := hq3 rfl
      rw [hcard, hf] at this
      norm_num at this
    · right
      exact ⟨q, rfl, by rw [hcard, hf]; norm_num⟩
  | B n q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hdvd' : orderBC n (2 ^ q.exponent) ∣ N8 := by rw [← hcard]; exact hdvd
    obtain ⟨hn2, hne⟩ := hr
    rcases orderBC_cases hn2 q.exponent_pos hdvd' with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
    · exfalso
      exact hne ⟨rfl, by rw [hcard, hf]; norm_num⟩
    · left
      show 3 = 3 ∧ q.card = 2
      exact ⟨rfl, by rw [hcard, hf]; norm_num⟩
  | C n q =>
    exfalso
    exact hr.2 (by simpa using hch)
  | D n q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hdvd' : orderD n (2 ^ q.exponent) ∣ N8 := by rw [← hcard]; exact hdvd
    obtain ⟨rfl, hf⟩ := orderD_cases hr q.exponent_pos hdvd'
    left
    show 3 = 3 ∧ q.card = 2
    exact ⟨rfl, by rw [hcard, hf]; norm_num⟩
  | twistedD n q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hdvd' : orderTwistedD n (2 ^ q.exponent) ∣ N8 := by rw [← hcard]; exact hdvd
    exact (orderTwistedD_false hr q.exponent_pos hdvd').elim
  | E6 q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hb := two_pow_pow_le ((orderE6_pow_dvd (q := 2 ^ q.exponent)
      (two_le_two_pow q.exponent_pos)).trans (by rw [← hcard]; exact hdvd))
    have := q.exponent_pos
    omega
  | E7 q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hb := two_pow_pow_le ((orderE7_pow_dvd (q := 2 ^ q.exponent)
      (two_le_two_pow q.exponent_pos)).trans (by rw [← hcard]; exact hdvd))
    have := q.exponent_pos
    omega
  | E8 q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hb := two_pow_pow_le ((orderE8_pow_dvd (2 ^ q.exponent)).trans
      (by rw [← hcard]; exact hdvd))
    have := q.exponent_pos
    omega
  | F4 q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hb := two_pow_pow_le ((orderF4_pow_dvd (2 ^ q.exponent)).trans
      (by rw [← hcard]; exact hdvd))
    have := q.exponent_pos
    omega
  | G2 q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hdvd' : orderG2 (2 ^ q.exponent) ∣ N8 := by rw [← hcard]; exact hdvd
    have hb := two_pow_pow_le ((orderG2_pow_dvd (2 ^ q.exponent)).trans hdvd')
    have hpos := q.exponent_pos
    have hf2 : q.exponent ≤ 2 := by omega
    have hf1 := gridG2 q.exponent (by simp; omega) hdvd'
    exfalso
    have h3 : 3 ≤ q.card := hr
    rw [hcard, hf1] at h3
    norm_num at h3
  | twistedE6 q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hb := two_pow_pow_le ((orderTwistedE6_pow_dvd (q := 2 ^ q.exponent)
      (two_le_two_pow q.exponent_pos)).trans (by rw [← hcard]; exact hdvd))
    have := q.exponent_pos
    omega
  | trialityD4 q =>
    have hcard := card_two_pow (q := q) (by simpa using hch)
    have hdvd' : orderTrialityD4 (2 ^ q.exponent) ∣ N8 := by rw [← hcard]; exact hdvd
    have hb := two_pow_pow_le ((orderTrialityD4_pow_dvd (2 ^ q.exponent)).trans hdvd')
    have hf1 : q.exponent = 1 := by have := q.exponent_pos; omega
    exfalso
    rw [hf1] at hdvd'
    revert hdvd'
    unfold orderTrialityD4 N8
    decide +kernel
  | suzuki m =>
    have hdvd' : orderSuzuki (2 ^ (2 * m + 1)) ∣ N8 := hdvd
    have hb := two_pow_pow_le ((orderSuzuki_pow_dvd (2 ^ (2 * m + 1))).trans hdvd')
    have hm2 : m ≤ 2 := by omega
    exact (gridSz m (by simp; omega) hdvd').elim
  | reeG2 m =>
    exfalso
    simp at hch
  | reeF4 m =>
    have hdvd' : orderTwistedF4 (2 ^ (2 * m + 1)) ∣ N8 := hdvd
    have hb := two_pow_pow_le ((orderTwistedF4_pow_dvd (2 ^ (2 * m + 1))).trans hdvd')
    omega
  | tits =>
    exfalso
    have hdvd' : orderTits ∣ N8 := hdvd
    revert hdvd'
    unfold orderTits N8
    decide +kernel

open CFSG.Yardstones.Md0ec50421ce4

theorem kLevel_le_two_of_k2 {S : Type} [Group S] (h : catalogIs S (k2 3)) : kLevel 3 S ≤ 2 := by
  unfold kLevel
  split_ifs <;> first | omega | exact absurd h ‹_›

theorem kLevel_le_one_of_chev3 {S : Type} [Group S] (h : IsChevSimple 3 S) : kLevel 3 S ≤ 1 := by
  unfold kLevel
  rw [if_pos h]

theorem kLevel_le_two_of_chev2
    {Q : Type} [Group Q] [Finite Q] (hQ : IsChevSimple 2 Q) (hdvd : Nat.card Q ∣ N8)
    (hA8 : ¬ Nonempty (Q ≃* alternatingGroup (Fin 8))) : kLevel 3 Q ≤ 2 := by
  rcases hQ with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic p hp => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      have hch : d.characteristic = 2 := hi
      have hcard : Nat.card Q = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d :=
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩ Q ⟨e⟩
      rcases chev2_index_good d hv hch (hcard ▸ hdvd) with hk | ⟨q, rfl, hq⟩
      · exact kLevel_le_two_of_k2 ⟨TauCeti.CFSGIndex.lie ⟨d, hv⟩, hk, ⟨e⟩⟩
      · have h3 : IsChevSimple 3 Q :=
          Or.inr ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩,
            (by show q.card = 2 ∧ 3 = 3; exact ⟨hq, rfl⟩), ⟨e⟩⟩
        have := kLevel_le_one_of_chev3 h3
        omega
  · cases i with
    | cyclic p hp => exact hi.elim
    | sporadic s => exact hi.elim
    | alternating n hn =>
      rcases hi with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact kLevel_le_two_of_k2 ⟨TauCeti.CFSGIndex.alternating 5 hn, Or.inl ⟨rfl, Or.inl rfl⟩, ⟨e⟩⟩
      · have h3 : IsChevSimple 3 Q :=
          Or.inr ⟨TauCeti.CFSGIndex.alternating 6 hn, by simp [ambiguousChev], ⟨e⟩⟩
        have := kLevel_le_one_of_chev3 h3
        omega
      · exact absurd ⟨e⟩ hA8
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r q =>
        rcases r with _ | _ | r
        · exact hi.elim
        · rcases hi with ⟨hq7, -⟩ | ⟨-, h23⟩
          · refine kLevel_le_two_of_k2 ⟨TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩, ?_, ⟨e⟩⟩
            show 3 = 3 ∧ ¬ 3 ∣ q.card
            rw [hq7]
            norm_num
          · exact absurd h23 (by norm_num)
        · exact hi.elim
      | twistedA r q =>
        rcases r with _ | _ | _ | _ | r
        · exact hi.elim
        · exact hi.elim
        · obtain ⟨hq3, -⟩ := hi
          have hp3 : q.p = 3 := by
            have h1 : q.p ∣ q.card := by
              rw [TauCeti.PrimePower.card_def]
              exact dvd_pow_self q.p q.exponent_pos.ne'
            rw [hq3] at h1
            exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 h1
          have h3 : IsChevSimple 3 Q :=
            Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩, (by simp only [onLie, TauCeti.LieTypeIndex.characteristic_twistedA]; exact hp3), ⟨e⟩⟩
          have := kLevel_le_one_of_chev3 h3
          omega
        · obtain ⟨-, h23⟩ := hi
          exact absurd h23 (by norm_num)
        · exact hi.elim
      | _ => exact hi.elim
    
end CFSG.LocalAnalysis.GLTheoremA.D4T
