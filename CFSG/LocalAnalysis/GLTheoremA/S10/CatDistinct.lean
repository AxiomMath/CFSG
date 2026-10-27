module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinctDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10

namespace CatDistinct

theorem even_two_pow' {k : ℕ} (hk : 1 ≤ k) : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h1 := even_two_pow' hk
  have h2 : 0 < 2 ^ k := by positivity
  exact Nat.odd_iff.2 (by omega)

theorem odd_two_pow_add_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k + 1) := by
  have h1 := even_two_pow' hk
  exact Nat.odd_iff.2 (by omega)

@[expose] def twP (r Q : ℕ) : ℕ := ∏ i ∈ Finset.Icc 2 (r + 1), (if Even i then Q ^ i - 1 else Q ^ i + 1)

theorem orderTwistedA_eq (r Q : ℕ) :
    orderTwistedA r Q = Q ^ (r * (r + 1) / 2) * twP r Q / Nat.gcd (r + 1) (Q + 1) := rfl

theorem odd_twP {r m : ℕ} (hm : 1 ≤ m) : Odd (twP r (2 ^ m)) := by
  unfold twP
  refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one (fun i hi => ?_)
  have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
  have hmi : 1 ≤ m * i := by nlinarith
  rw [← pow_mul]
  split_ifs
  · exact odd_two_pow_sub_one hmi
  · exact odd_two_pow_add_one hmi

theorem gcd_dvd_twP {r Q : ℕ} (hr : 1 ≤ r) (hQ : 1 ≤ Q) : Nat.gcd (r + 1) (Q + 1) ∣ twP r Q := by
  refine (Nat.gcd_dvd_right _ _).trans ?_
  have h2 : (Q + 1) ∣ Q ^ 2 - 1 := by
    obtain ⟨c, rfl⟩ : ∃ c, Q = c + 1 := ⟨Q - 1, by omega⟩
    have : (c + 1) ^ 2 - 1 = (c + 1 + 1) * c := by
      have : (c + 1) ^ 2 = (c + 1 + 1) * c + 1 := by ring
      omega
    exact ⟨c, this⟩
  refine h2.trans ?_
  have hmem : 2 ∈ Finset.Icc 2 (r + 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have := Finset.dvd_prod_of_mem (fun i => if Even i then Q ^ i - 1 else Q ^ i + 1) hmem
  unfold twP
  simpa using this

theorem sum_Icc_two (r : ℕ) : ∑ i ∈ Finset.Icc 2 (r + 1), i * 2 = r * (r + 3) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    ring

theorem twP_le (r Q : ℕ) (hQ : 1 ≤ Q) : twP r Q ≤ 2 ^ r * Q ^ (r * (r + 3) / 2) := by
  have hS : ∑ i ∈ Finset.Icc 2 (r + 1), i = r * (r + 3) / 2 := by
    have h := sum_Icc_two r
    rw [← Finset.sum_mul] at h
    omega
  unfold twP
  calc ∏ i ∈ Finset.Icc 2 (r + 1), (if Even i then Q ^ i - 1 else Q ^ i + 1)
      ≤ ∏ i ∈ Finset.Icc 2 (r + 1), (2 * Q ^ i) := by
        refine Finset.prod_le_prod (fun i _ => ?_)
        have : 1 ≤ Q ^ i := Nat.one_le_pow _ _ hQ
        split_ifs <;> omega
    _ = 2 ^ r * Q ^ (r * (r + 3) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, hS]
        simp


theorem four_dvd_two_pow {k : ℕ} (hk : 2 ≤ k) : 4 ∣ 2 ^ k := by
  have : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [this]
  exact pow_dvd_pow 2 hk

theorem two_pow_mul_odd_inj {u v A B : ℕ} (hA : Odd A) (hB : Odd B) (h : 2 ^ u * A = 2 ^ v * B) :
    u = v ∧ A = B := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, v = u + (d + 1) := ⟨v - u - 1, by omega⟩
    rw [pow_add, mul_assoc] at h
    have h2 : A = 2 ^ (d + 1) * B := Nat.eq_of_mul_eq_mul_left (by positivity) h
    have : Even A := by
      rw [h2]
      exact (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right B
    exact (Nat.not_even_iff_odd.2 hA) this
  · exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, u = v + (d + 1) := ⟨u - v - 1, by omega⟩
    rw [pow_add, mul_assoc] at h
    have h2 : B = 2 ^ (d + 1) * A := Nat.eq_of_mul_eq_mul_left (by positivity) h.symm
    have : Even B := by
      rw [h2]
      exact (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right A
    exact (Nat.not_even_iff_odd.2 hB) this

theorem urn_size {r n : ℕ} (hr : 2 ≤ r) (hn : 3 ≤ n) :
    2 ^ r * (2 ^ n) ^ (r * (r + 3) / 2) + 1 < (2 ^ n) ^ (r * (r + 1)) := by
  obtain ⟨S, hS⟩ : ∃ S, S = r * (r + 3) / 2 := ⟨_, rfl⟩
  have h2S : 2 * S = r * (r + 3) := by
    have : r * (r + 3) = 2 * (r * (r + 3) / 2) := by
      have h : Even (r * (r + 3)) := by
        rcases Nat.even_or_odd r with h | h
        · exact h.mul_right _
        · exact (h.add_odd (by decide : Odd 3)).mul_left _
      obtain ⟨c, hc⟩ := h
      omega
    omega
  obtain ⟨t, ht⟩ : ∃ t, t + S = r * (r + 1) := ⟨r * (r + 1) - S, by
    have : S ≤ r * (r + 1) := by nlinarith
    omega⟩
  have h3t : r + 1 ≤ 3 * t := by nlinarith
  have hQ : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [← hS, ← ht, add_comm t S, pow_add]
  have h1 : 2 ^ (r + 1) ≤ (2 ^ n) ^ t := by
    calc 2 ^ (r + 1) ≤ 2 ^ (3 * t) := Nat.pow_le_pow_right (by norm_num) h3t
      _ = 8 ^ t := by rw [pow_mul]; norm_num
      _ ≤ (2 ^ n) ^ t := Nat.pow_le_pow_left hQ t
  have hS1 : 1 ≤ S := by
    by_contra h
    have : S = 0 := by omega
    rw [this] at h2S
    nlinarith
  have hQS : 2 ≤ (2 ^ n) ^ S := by
    calc 2 ≤ 8 := by norm_num
      _ ≤ 2 ^ n := hQ
      _ = (2 ^ n) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ n) ^ S := Nat.pow_le_pow_right (by positivity) hS1
  have h4 : 2 ^ r * 2 ≤ 2 ^ (r + 1) := by rw [pow_succ]
  calc 2 ^ r * (2 ^ n) ^ S + 1 < 2 ^ r * (2 ^ n) ^ S + (2 ^ n) ^ S := by omega
    _ ≤ 2 ^ r * (2 ^ n) ^ S + 2 ^ r * (2 ^ n) ^ S := by
        have : (2 ^ n) ^ S ≤ 2 ^ r * (2 ^ n) ^ S := by
          have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
          nlinarith
        omega
    _ = 2 * (2 ^ r * (2 ^ n) ^ S) := by ring
    _ = (2 ^ r * 2) * (2 ^ n) ^ S := by ring
    _ ≤ 2 ^ (r + 1) * (2 ^ n) ^ S := Nat.mul_le_mul_right _ h4
    _ ≤ (2 ^ n) ^ t * (2 ^ n) ^ S := Nat.mul_le_mul_right _ h1
    _ = (2 ^ n) ^ S * (2 ^ n) ^ t := mul_comm _ _

theorem four_dvd_pow_two_mul {a j : ℕ} (ha : 1 ≤ a) (hj : 2 ≤ j) : 4 ∣ (2 ^ a) ^ j := by
  rw [← pow_mul]
  exact four_dvd_two_pow (by nlinarith)

theorem odd_pow_two_pow_sub_one {a j : ℕ} (ha : 1 ≤ a) (hj : 1 ≤ j) : Odd ((2 ^ a) ^ j - 1) := by
  rw [← pow_mul]
  exact odd_two_pow_sub_one (by nlinarith)

theorem odd_pow_two_pow_add_one {a j : ℕ} (ha : 1 ≤ a) (hj : 1 ≤ j) : Odd ((2 ^ a) ^ j + 1) := by
  rw [← pow_mul]
  exact odd_two_pow_add_one (by nlinarith)

theorem orderTwistedA_mul_gcd {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    orderTwistedA r (2 ^ m) * Nat.gcd (r + 1) (2 ^ m + 1) =
      2 ^ (m * (r * (r + 1) / 2)) * twP r (2 ^ m) := by
  rw [orderTwistedA_eq, Nat.div_mul_cancel ((gcd_dvd_twP hr (Nat.one_le_two_pow)).mul_left _), ← pow_mul]

theorem odd_gcd_twisted {r m : ℕ} (hm : 1 ≤ m) : Odd (Nat.gcd (r + 1) (2 ^ m + 1)) :=
  Odd.of_dvd_nat (odd_two_pow_add_one hm) (Nat.gcd_dvd_right _ _)

theorem one_le_gcd_twisted {r Q : ℕ} : 1 ≤ Nat.gcd (r + 1) (Q + 1) :=
  Nat.gcd_pos_of_pos_left _ (by omega)

theorem orderG2_two_pow {a : ℕ} (ha : 1 ≤ a) :
    ∃ O, Odd O ∧ orderG2 (2 ^ a) = 2 ^ (a * 6) * O :=
  ⟨((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1),
    (odd_pow_two_pow_sub_one ha (by norm_num)).mul (odd_pow_two_pow_sub_one ha (by norm_num)),
    by simp only [orderG2]; rw [pow_mul 2 a 6, mul_assoc]⟩

theorem orderTrialityD4_two_pow {a : ℕ} (ha : 1 ≤ a) :
    ∃ O, Odd O ∧ O % 4 = 1 ∧ orderTrialityD4 (2 ^ a) = 2 ^ (a * 12) * O := by
  have h8 := four_dvd_pow_two_mul ha (by norm_num : 2 ≤ 8)
  have h4 := four_dvd_pow_two_mul ha (by norm_num : 2 ≤ 4)
  have h6 := four_dvd_pow_two_mul ha (by norm_num : 2 ≤ 6)
  have h2 := four_dvd_pow_two_mul ha (by norm_num : 2 ≤ 2)
  have p6 : 1 ≤ (2 ^ a) ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have p2 : 1 ≤ (2 ^ a) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have e1 : ((2 ^ a) ^ 8 + (2 ^ a) ^ 4 + 1) % 4 = 1 := by omega
  have e2 : ((2 ^ a) ^ 6 - 1) % 4 = 3 := by omega
  have e3 : ((2 ^ a) ^ 2 - 1) % 4 = 3 := by omega
  have hmod : (((2 ^ a) ^ 8 + (2 ^ a) ^ 4 + 1) * ((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1)) % 4 = 1 := by
    rw [Nat.mul_mod, Nat.mul_mod ((2 ^ a) ^ 8 + (2 ^ a) ^ 4 + 1), e1, e2, e3]
  refine ⟨((2 ^ a) ^ 8 + (2 ^ a) ^ 4 + 1) * ((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1),
    Nat.odd_iff.2 (by omega), hmod, ?_⟩
  simp only [orderTrialityD4]
  rw [pow_mul 2 a 12, mul_assoc, mul_assoc, mul_assoc]

theorem orderA_one_two_pow {k : ℕ} (hk : 1 ≤ k) :
    ∃ O, Odd O ∧ O % 4 = 3 ∧ orderA 1 (2 ^ k) = 2 ^ k * O := by
  have hg : Nat.gcd (1 + 1) (2 ^ k - 1) = 1 := by
    have : Odd (2 ^ k - 1) := odd_two_pow_sub_one hk
    exact Nat.coprime_two_left.2 this
  refine ⟨(2 ^ k) ^ 2 - 1, odd_pow_two_pow_sub_one hk (by norm_num), ?_, ?_⟩
  · have h2 := four_dvd_pow_two_mul hk (by norm_num : 2 ≤ 2)
    have p2 : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega
  · simp [orderA, hg]

theorem twP_two (Q : ℕ) : twP 2 Q = (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
  simp [twP, Finset.prod_Icc_succ_top, Nat.even_iff]

theorem twP_five (Q : ℕ) :
    twP 5 Q = (Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1) * (Q ^ 5 + 1) * (Q ^ 6 - 1) := by
  simp [twP, Finset.prod_Icc_succ_top, Nat.even_iff]

theorem orderA_two_mul_gcd (Q : ℕ) :
    orderA 2 Q * Nat.gcd 3 (Q - 1) = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
  have hdvd : Nat.gcd 3 (Q - 1) ∣ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
    have h1 : (Q - 1) ∣ Q ^ 3 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow Q 1 3
    exact (Nat.gcd_dvd_right 3 (Q - 1)).trans (h1.trans ((Dvd.intro_left _ rfl).trans (Dvd.intro_left _ rfl)))
  simp only [orderA]
  have : (∏ i ∈ Finset.Icc 2 (2 + 1), (Q ^ i - 1)) = (Q ^ 2 - 1) * (Q ^ 3 - 1) := by
    simp [Finset.prod_Icc_succ_top]
  rw [this]
  norm_num
  exact Nat.div_mul_cancel hdvd

theorem mod_four_sq {b : ℕ} (hb : 1 ≤ b) : ((2 ^ b) ^ 2 - 1) % 4 = 3 := by
  have h2 := four_dvd_pow_two_mul hb (by norm_num : 2 ≤ 2)
  have p2 : 1 ≤ (2 ^ b) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  omega

theorem mod_four_cube_sub {b : ℕ} (hb : 1 ≤ b) : ((2 ^ b) ^ 3 - 1) % 4 = 3 := by
  have h2 := four_dvd_pow_two_mul hb (by norm_num : 2 ≤ 3)
  have p2 : 1 ≤ (2 ^ b) ^ 3 := Nat.one_le_pow _ _ (by positivity)
  omega

theorem mod_four_cube_add {b : ℕ} (hb : 1 ≤ b) : ((2 ^ b) ^ 3 + 1) % 4 = 1 := by
  have h2 := four_dvd_pow_two_mul hb (by norm_num : 2 ≤ 3)
  omega

theorem td4_ne_L2 {a k : ℕ} (ha : 1 ≤ a) (hk : 1 ≤ k) :
    orderTrialityD4 (2 ^ a) ≠ orderA 1 (2 ^ k) := by
  intro h
  obtain ⟨O₁, hO₁, hm₁, e₁⟩ := orderTrialityD4_two_pow ha
  obtain ⟨O₂, hO₂, hm₂, e₂⟩ := orderA_one_two_pow hk
  rw [e₁, e₂] at h
  have := (two_pow_mul_odd_inj hO₁ hO₂ h).2
  omega

theorem td4_ne_A2 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    orderTrialityD4 (2 ^ a) ≠ orderA 2 (2 ^ b) := by
  intro h
  obtain ⟨O₁, hO₁, hm₁, e₁⟩ := orderTrialityD4_two_pow ha
  have hg := orderA_two_mul_gcd (2 ^ b)
  rw [← h, e₁] at hg
  have hodd_g : Odd (Nat.gcd 3 (2 ^ b - 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left _ _)
  have hP : Odd (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1)) :=
    (odd_pow_two_pow_sub_one hb (by norm_num)).mul (odd_pow_two_pow_sub_one hb (by norm_num))
  have hg' : 2 ^ (a * 12) * (O₁ * Nat.gcd 3 (2 ^ b - 1)) =
      2 ^ (b * 3) * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1)) := by
    rw [← mul_assoc, hg, ← pow_mul]
  obtain ⟨h12, hprod⟩ := two_pow_mul_odd_inj (hO₁.mul hodd_g) hP hg'
  have hb4 : b = 4 * a := by omega
  have hQ3 : (2 ^ b) % 3 = 1 := by
    rw [hb4, pow_mul]
    norm_num [Nat.pow_mod]
  have hQpos : 0 < 2 ^ b := by positivity
  have hg3 : Nat.gcd 3 (2 ^ b - 1) = 3 := by
    apply Nat.gcd_eq_left
    omega
  rw [hg3] at hprod
  have e1 := mod_four_sq hb
  have e2 := mod_four_cube_sub hb
  have h4 := congrArg (· % 4) hprod
  simp only [Nat.mul_mod O₁ 3, Nat.mul_mod (((2 ^ b) ^ 2 - 1)), hm₁, e1, e2] at h4
  omega

theorem td4_ne_U3 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    orderTrialityD4 (2 ^ a) ≠ orderTwistedA 2 (2 ^ b) := by
  intro h
  obtain ⟨O₁, hO₁, hm₁, e₁⟩ := orderTrialityD4_two_pow ha
  have hg := orderTwistedA_mul_gcd (r := 2) (m := b) (by norm_num) hb
  rw [← h, e₁, twP_two] at hg
  have hodd_g : Odd (Nat.gcd (2 + 1) (2 ^ b + 1)) := odd_gcd_twisted hb
  have hP : Odd (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1)) :=
    (odd_pow_two_pow_sub_one hb (by norm_num)).mul (odd_pow_two_pow_add_one hb (by norm_num))
  have hg' : 2 ^ (a * 12) * (O₁ * Nat.gcd (2 + 1) (2 ^ b + 1)) =
      2 ^ (b * 3) * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1)) := by
    rw [← mul_assoc, hg]
  obtain ⟨h12, hprod⟩ := two_pow_mul_odd_inj (hO₁.mul hodd_g) hP hg'
  have hb4 : b = 4 * a := by omega
  have hQ3 : (2 ^ b) % 3 = 1 := by
    rw [hb4, pow_mul]
    norm_num [Nat.pow_mod]
  have hg3 : Nat.gcd (2 + 1) (2 ^ b + 1) = 1 := by
    have : Nat.Coprime (2 + 1) (2 ^ b + 1) := by
      rw [Nat.coprime_comm, Nat.Coprime, Nat.gcd_comm]
      show Nat.gcd 3 (2 ^ b + 1) = 1
      have h3 : ¬ 3 ∣ 2 ^ b + 1 := by omega
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    exact this
  rw [hg3] at hprod
  have e1 := mod_four_sq hb
  have e2 := mod_four_cube_add hb
  have h4 := congrArg (· % 4) hprod
  simp only [mul_one, Nat.mul_mod (((2 ^ b) ^ 2 - 1)), hm₁, e1, e2] at h4
  omega

theorem td4_ne_U6 {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) (hodd : Odd m) :
    orderTrialityD4 (2 ^ a) ≠ orderTwistedA 5 (2 ^ m) := by
  intro h
  obtain ⟨O₁, hO₁, hm₁, e₁⟩ := orderTrialityD4_two_pow ha
  have hg := orderTwistedA_mul_gcd (r := 5) (m := m) (by norm_num) hm
  rw [← h, e₁] at hg
  have hg' : 2 ^ (a * 12) * (O₁ * Nat.gcd (5 + 1) (2 ^ m + 1)) =
      2 ^ (m * (5 * (5 + 1) / 2)) * twP 5 (2 ^ m) := by rw [← mul_assoc, hg]
  have := (two_pow_mul_odd_inj (hO₁.mul (odd_gcd_twisted hm)) (odd_twP hm) hg').1
  obtain ⟨c, hc⟩ := hodd
  norm_num at this
  omega

theorem g2_ne_U6 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (h : n = m ∨ Odd m) :
    orderG2 (2 ^ n) ≠ orderTwistedA 5 (2 ^ m) := by
  intro hh
  obtain ⟨O₁, hO₁, e₁⟩ := orderG2_two_pow hn
  have hg := orderTwistedA_mul_gcd (r := 5) (m := m) (by norm_num) hm
  rw [← hh, e₁] at hg
  have hg' : 2 ^ (n * 6) * (O₁ * Nat.gcd (5 + 1) (2 ^ m + 1)) =
      2 ^ (m * (5 * (5 + 1) / 2)) * twP 5 (2 ^ m) := by rw [← mul_assoc, hg]
  have := (two_pow_mul_odd_inj (hO₁.mul (odd_gcd_twisted hm)) (odd_twP hm) hg').1
  norm_num at this
  rcases h with rfl | ⟨c, hc⟩ <;> omega

theorem g2_inj_arith {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h : orderG2 (2 ^ n) = orderG2 (2 ^ n')) : n = n' := by
  obtain ⟨O₁, hO₁, e₁⟩ := orderG2_two_pow hn
  obtain ⟨O₂, hO₂, e₂⟩ := orderG2_two_pow hn'
  rw [e₁, e₂] at h
  have := (two_pow_mul_odd_inj hO₁ hO₂ h).1
  omega

theorem u33_ne_U6 {m : ℕ} (hm : 1 ≤ m) : (6048 : ℕ) ≠ orderTwistedA 5 (2 ^ m) := by
  intro h
  have hg := orderTwistedA_mul_gcd (r := 5) (m := m) (by norm_num) hm
  rw [← h] at hg
  have hg' : 2 ^ 5 * (189 * Nat.gcd (5 + 1) (2 ^ m + 1)) =
      2 ^ (m * (5 * (5 + 1) / 2)) * twP 5 (2 ^ m) := by rw [← hg]; ring
  have := (two_pow_mul_odd_inj ((by decide : Odd 189).mul (odd_gcd_twisted hm)) (odd_twP hm) hg').1
  norm_num at this
  omega

theorem orderA_one_eq {k : ℕ} (hk : 1 ≤ k) : orderA 1 (2 ^ k) = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
  have hg : Nat.gcd (1 + 1) (2 ^ k - 1) = 1 := Nat.coprime_two_left.2 (odd_two_pow_sub_one hk)
  simp [orderA, hg]

theorem u4_ne_L2 {k : ℕ} (hk : 1 ≤ k) : (25920 : ℕ) ≠ orderA 1 (2 ^ k) := by
  intro h
  have h1 : (25920 : ℕ) = 2 ^ 6 * 405 := by norm_num
  obtain ⟨O₂, hO₂, hm₂, e₂⟩ := orderA_one_two_pow hk
  rw [h1, e₂] at h
  have := (two_pow_mul_odd_inj (by decide) hO₂ h).2
  omega

theorem u5_ne_L2 {k : ℕ} (hk : 1 ≤ k) : (13685760 : ℕ) ≠ orderA 1 (2 ^ k) := by
  intro h
  have h1 : (13685760 : ℕ) = 2 ^ 10 * 13365 := by norm_num
  obtain ⟨O₂, hO₂, hm₂, e₂⟩ := orderA_one_two_pow hk
  rw [h1, e₂] at h
  have := (two_pow_mul_odd_inj (by decide) hO₂ h).2
  omega

theorem urn_ne_L2 {r n k : ℕ} (hr : 2 ≤ r) (hn : 3 ≤ n) (hk : 1 ≤ k) :
    orderTwistedA r (2 ^ n) ≠ orderA 1 (2 ^ k) := by
  intro h
  have hn1 : 1 ≤ n := by omega
  have hg := orderTwistedA_mul_gcd (r := r) (m := n) (by omega) hn1
  rw [h, orderA_one_eq hk] at hg
  have hg' : 2 ^ k * (((2 ^ k) ^ 2 - 1) * Nat.gcd (r + 1) (2 ^ n + 1)) =
      2 ^ (n * (r * (r + 1) / 2)) * twP r (2 ^ n) := by rw [← mul_assoc, hg]
  have hO : Odd ((2 ^ k) ^ 2 - 1) := odd_pow_two_pow_sub_one (a := k) (j := 2) hk (by norm_num)
  obtain ⟨hke, hP⟩ := two_pow_mul_odd_inj (hO.mul (odd_gcd_twisted hn1)) (odd_twP hn1) hg'
  have hle := twP_le r (2 ^ n) Nat.one_le_two_pow
  have hsize := urn_size hr hn
  have h2e : r * (r + 1) / 2 * 2 = r * (r + 1) := Nat.div_mul_cancel (Nat.even_mul_succ_self r).two_dvd
  have hk2 : (2 ^ k) ^ 2 = (2 ^ n) ^ (r * (r + 1)) := by
    rw [← pow_mul, ← pow_mul, hke, mul_assoc, h2e]
  have hg1 : 1 ≤ Nat.gcd (r + 1) (2 ^ n + 1) := one_le_gcd_twisted
  have : (2 ^ k) ^ 2 - 1 ≤ ((2 ^ k) ^ 2 - 1) * Nat.gcd (r + 1) (2 ^ n + 1) := Nat.le_mul_of_pos_right _ hg1
  rw [hP] at this
  rw [hk2] at this
  omega

theorem orderTrialityD4_ge {c : ℕ} (hc : 2 ≤ c) : c ^ 20 ≤ orderTrialityD4 c := by
  unfold orderTrialityD4
  have h1 : c ^ 8 ≤ c ^ 8 + c ^ 4 + 1 := by omega
  have h6 : 1 ≤ c ^ 6 - 1 := by
    have : 2 ^ 6 ≤ c ^ 6 := Nat.pow_le_pow_left hc 6
    omega
  have h2 : 1 ≤ c ^ 2 - 1 := by
    have : 2 ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left hc 2
    omega
  calc c ^ 20 = c ^ 12 * c ^ 8 * 1 * 1 := by ring
    _ ≤ c ^ 12 * (c ^ 8 + c ^ 4 + 1) * (c ^ 6 - 1) * (c ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl h1) h6) h2

theorem orderTrialityD4_gt {c : ℕ} (hc : 2 ≤ c) : 1048576 ≤ orderTrialityD4 c := by
  have := orderTrialityD4_ge hc
  have h2 : 2 ^ 20 ≤ c ^ 20 := Nat.pow_le_pow_left hc 20
  norm_num at h2
  omega

theorem orderG2_ge {c : ℕ} (hc : 3 ≤ c) : 4245696 ≤ orderG2 c := by
  unfold orderG2
  have h6 : 3 ^ 6 ≤ c ^ 6 := Nat.pow_le_pow_left hc 6
  have h2 : 3 ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left hc 2
  norm_num at h6 h2
  calc 4245696 = 729 * 728 * 8 := by norm_num
    _ ≤ c ^ 6 * (c ^ 6 - 1) * (c ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h6 (by omega)) (by omega)

theorem td4_ne_ys09 {c : ℕ} (hc : 2 ≤ c) :
    orderTrialityD4 c ≠ 13685760 ∧ orderTrialityD4 c ≠ 9196830720 ∧
      orderTrialityD4 c ≠ 47377612800 ∧ orderTrialityD4 c ≠ 174182400 := by
  by_cases h8 : 8 ≤ c
  · have h := orderTrialityD4_ge hc
    have : 8 ^ 20 ≤ c ^ 20 := Nat.pow_le_pow_left h8 20
    norm_num at this
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · have : c ≤ 7 := by omega
    interval_cases c <;> decide

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)

abbrev OrderBridge : Prop :=
  ∀ (idx : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G],
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie idx).Group) → Nat.card G = lieOrderFormula idx.1

abbrev EvenLieModel : Prop :=
  ∀ (S : Type) [Group S] (d : TauCeti.ValidLieTypeIndex), d.1.characteristic = 2 →
    S ≃* d.Group → ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel S t n 2 f

structure Ctx : Prop where
  bridge : OrderBridge
  formulas : LieOrderFormulasInput
  even : EvenLieModel
  m22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520

theorem xc (hc : Ctx) {S : Type} [Group S] [Finite S] {t' : StatedLieTag} {n' p g : ℕ}
    (hex : ¬ (t' = .PSL ∧ n' = 2) ∧ ¬ (t' = .PSp ∧ n' = 2))
    (hadm' : StatedLieAdmissible t' n' p g) (hp2 : p ≠ 2)
    (hM' : Nat.card S * lieOrderDivisor t' n' (p ^ g) = lieOrderNumerator t' n' (p ^ g))
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2) (e : S ≃* d.Group) : False := by
  obtain ⟨t, n, f, hX⟩ := hc.even S d hd e
  have hadm := CFSG.SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hX
  have hM := (hc.formulas S t n 2 f hadm hX).2.1
  rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadm hadm' hp2 hM hM' with
    ⟨-, -, -, h1, h2, -⟩ | ⟨-, -, -, h1, h2, -⟩ | ⟨-, -, -, h1, h2, -⟩
  exacts [hex.1 ⟨h1, h2⟩, hex.1 ⟨h1, h2⟩, hex.2 ⟨h1, h2⟩]

theorem hM'_of_card {S : Type} {t : StatedLieTag} {n p g : ℕ} (hadm : StatedLieAdmissible t n p g)
    (hcard : Nat.card S = lieOrderNumerator t n (p ^ g) / lieOrderDivisor t n (p ^ g)) :
    Nat.card S * lieOrderDivisor t n (p ^ g) = lieOrderNumerator t n (p ^ g) := by
  rw [hcard]
  exact Nat.div_mul_cancel (CFSG.ComponentClassification.CatLeafProof.lieOrderDivisor_dvd_numerator hadm)

theorem td4_odd_not_even (hc : Ctx) {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq : q.p ≠ 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2) (f : S ≃* d.Group) : False := by
  have hcard : Nat.card S = orderTrialityD4 q.card := hc.bridge ⟨.trialityD4 q, hv⟩ S ⟨e⟩
  have hadm : StatedLieAdmissible .trialityD4 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
  refine xc hc (t' := .trialityD4) (n' := 0) (by simp) hadm hq ?_ d hd f
  refine hM'_of_card hadm ?_
  rw [hcard]
  simp [orderTrialityD4, lieOrderNumerator, lieOrderDivisor, TauCeti.PrimePower.card_def]

theorem g2_odd_not_even (hc : Ctx) {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq : q.p ≠ 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2) (f : S ≃* d.Group) : False := by
  have hcard : Nat.card S = orderG2 q.card := hc.bridge ⟨.G2 q, hv⟩ S ⟨e⟩
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
  have hadm : StatedLieAdmissible .G2 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl, h3⟩
  refine xc hc (t' := .G2) (n' := 0) (by simp) hadm hq ?_ d hd f
  refine hM'_of_card hadm ?_
  rw [hcard]
  simp [orderG2, lieOrderNumerator, lieOrderDivisor, TauCeti.PrimePower.card_def]

theorem two_le_card (q : TauCeti.PrimePower) : 2 ≤ q.card := by
  have h1 := q.prime_p.two_le
  have h2 : q.p ≤ q.p ^ q.exponent := Nat.le_self_pow q.exponent_pos.ne' q.p
  rw [TauCeti.PrimePower.card_def]
  omega

theorem card_isU4two (hb : OrderBridge) {S : Type} [Group S] [Finite S] (h : catalogIs S S9.isU4two) :
    Nat.card S = 25920 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isU4two, onLie] at hi
  | alternating n hn => simp [S9.isU4two, onLie] at hi
  | sporadic s => simp [S9.isU4two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r <;> simp [S9.isU4two, onLie] at hi
      rw [hb ⟨.twistedA 3 q, hv⟩ S ⟨e⟩]
      show orderTwistedA 3 q.card = 25920
      rw [(TauCeti.PrimePower.card_def q).trans hi]
      decide
    | _ => simp [S9.isU4two, onLie] at hi

theorem card_isU5two (hb : OrderBridge) {S : Type} [Group S] [Finite S] (h : catalogIs S S9.isU5two) :
    Nat.card S = 13685760 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isU5two, onLie] at hi
  | alternating n hn => simp [S9.isU5two, onLie] at hi
  | sporadic s => simp [S9.isU5two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | r <;> simp [S9.isU5two, onLie] at hi
      rw [hb ⟨.twistedA 4 q, hv⟩ S ⟨e⟩]
      show orderTwistedA 4 q.card = 13685760
      rw [(TauCeti.PrimePower.card_def q).trans hi]
      decide
    | _ => simp [S9.isU5two, onLie] at hi

theorem card_isU6two (hb : OrderBridge) {S : Type} [Group S] [Finite S] (h : catalogIs S S9.isU6two) :
    Nat.card S = 9196830720 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isU6two, onLie] at hi
  | alternating n hn => simp [S9.isU6two, onLie] at hi
  | sporadic s => simp [S9.isU6two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r <;> simp [S9.isU6two, onLie] at hi
      rw [hb ⟨.twistedA 5 q, hv⟩ S ⟨e⟩]
      show orderTwistedA 5 q.card = 9196830720
      rw [(TauCeti.PrimePower.card_def q).trans hi]
      decide
    | _ => simp [S9.isU6two, onLie] at hi

theorem card_isSp8two (hb : OrderBridge) {S : Type} [Group S] [Finite S] (h : catalogIs S S9.isSp8two) :
    Nat.card S = 47377612800 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isSp8two, onLie] at hi
  | alternating n hn => simp [S9.isSp8two, onLie] at hi
  | sporadic s => simp [S9.isSp8two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | B r q =>
      rcases r with _ | _ | _ | _ | _ | r <;> simp [S9.isSp8two, onLie] at hi
      rw [hb ⟨.B 4 q, hv⟩ S ⟨e⟩]
      show orderBC 4 q.card = 47377612800
      rw [(TauCeti.PrimePower.card_def q).trans hi]
      decide
    | _ => simp [S9.isSp8two, onLie] at hi

theorem card_isD4two (hb : OrderBridge) {S : Type} [Group S] [Finite S] (h : catalogIs S S9.isD4two) :
    Nat.card S = 174182400 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isD4two, onLie] at hi
  | alternating n hn => simp [S9.isD4two, onLie] at hi
  | sporadic s => simp [S9.isD4two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D r q =>
      rcases r with _ | _ | _ | _ | _ | r <;> simp [S9.isD4two, onLie] at hi
      rw [hb ⟨.D 4 q, hv⟩ S ⟨e⟩]
      show orderD 4 q.card = 174182400
      rw [(TauCeti.PrimePower.card_def q).trans hi]
      decide
    | _ => simp [S9.isD4two, onLie] at hi

theorem card_isU33 (hb : OrderBridge) {S : Type} [Group S] [Finite S] (h : catalogIs S isU33) :
    Nat.card S = 6048 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [isU33, onLie] at hi
  | alternating n hn => simp [isU33, onLie] at hi
  | sporadic s => simp [isU33, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | r <;> simp [isU33, onLie] at hi
      rw [hb ⟨.twistedA 2 q, hv⟩ S ⟨e⟩]
      show orderTwistedA 2 q.card = 6048
      rw [(TauCeti.PrimePower.card_def q).trans hi]
      decide
    | _ => simp [isU33, onLie] at hi

theorem urn_ne_60 {r n : ℕ} (hr : 2 ≤ r) (hn : 3 ≤ n) : orderTwistedA r (2 ^ n) ≠ 60 := by
  intro h
  have hn1 : 1 ≤ n := by omega
  have hg := orderTwistedA_mul_gcd (r := r) (m := n) (by omega) hn1
  rw [h] at hg
  have hg' : 2 ^ 2 * (15 * Nat.gcd (r + 1) (2 ^ n + 1)) =
      2 ^ (n * (r * (r + 1) / 2)) * twP r (2 ^ n) := by rw [← hg]; ring
  have h2 := (two_pow_mul_odd_inj ((by decide : Odd 15).mul (odd_gcd_twisted hn1)) (odd_twP hn1) hg').1
  have h6 : 6 ≤ r * (r + 1) := by nlinarith
  have h3 : 3 ≤ r * (r + 1) / 2 := by omega
  nlinarith

theorem card_alternating_of_iso {S : Type} [Group S] {n : ℕ} (hn : 5 ≤ n)
    (e : S ≃* (TauCeti.CFSGIndex.alternating n hn).Group) : Nat.card S = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [Nat.card_congr e.toEquiv]
  show Nat.card (alternatingGroup (Fin n)) = _
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

def CharTwo (S : Type) [Group S] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (S ≃* d.Group)

theorem data_isG2n (hc : Ctx) {S : Type} [Group S] [Finite S] {n : ℕ} (h : catalogIs S (isG2n n)) :
    1 ≤ n ∧ Nat.card S = orderG2 (2 ^ n) ∧ CharTwo S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [isG2n, onLie] at hi
  | alternating m hm => simp [isG2n, onLie] at hi
  | sporadic s => simp [isG2n, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | G2 q =>
      simp only [isG2n, onLie] at hi
      obtain ⟨hp, hn⟩ := hi
      refine ⟨by have := q.exponent_pos; omega, ?_, ⟨⟨.G2 q, hv⟩, by simp [hp], ⟨e⟩⟩⟩
      rw [hc.bridge ⟨.G2 q, hv⟩ S ⟨e⟩]
      show orderG2 q.card = _
      rw [TauCeti.PrimePower.card_def, hp, hn]
    | _ => simp [isG2n, onLie] at hi

theorem data_isU6n (hc : Ctx) {S : Type} [Group S] [Finite S] {m : ℕ} (h : catalogIs S (isU6n m)) :
    1 ≤ m ∧ Nat.card S = orderTwistedA 5 (2 ^ m) ∧ CharTwo S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [isU6n, onLie] at hi
  | alternating k hk => simp [isU6n, onLie] at hi
  | sporadic s => simp [isU6n, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r <;> simp [isU6n, onLie] at hi
      obtain ⟨hp, hn⟩ := hi
      refine ⟨by have := q.exponent_pos; omega, ?_, ⟨⟨.twistedA 5 q, hv⟩, by simp [hp], ⟨e⟩⟩⟩
      rw [hc.bridge ⟨.twistedA 5 q, hv⟩ S ⟨e⟩]
      show orderTwistedA 5 q.card = _
      rw [TauCeti.PrimePower.card_def, hp, hn]
    | _ => simp [isU6n, onLie] at hi

theorem data_isUrn (hc : Ctx) {S : Type} [Group S] [Finite S] {n : ℕ} (h : catalogIs S (isUrn n)) :
    ∃ r : ℕ, 2 ≤ r ∧ 1 ≤ n ∧ Nat.card S = orderTwistedA r (2 ^ n) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [isUrn, onLie] at hi
  | alternating k hk => simp [isUrn, onLie] at hi
  | sporadic s => simp [isUrn, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      simp only [isUrn, onLie] at hi
      obtain ⟨hr, hp, hn⟩ := hi
      refine ⟨r, hr, by have := q.exponent_pos; omega, ?_⟩
      rw [hc.bridge ⟨.twistedA r q, hv⟩ S ⟨e⟩]
      show orderTwistedA r q.card = _
      rw [TauCeti.PrimePower.card_def, hp, hn]
    | _ => simp [isUrn, onLie] at hi

theorem data_isL2n (hc : Ctx) {S : Type} [Group S] [Finite S] {k : ℕ} (h : catalogIs S (isL2n k)) :
    Nat.card S = 60 ∨ (1 ≤ k ∧ Nat.card S = orderA 1 (2 ^ k) ∧ CharTwo S) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [isL2n] at hi
  | alternating m hm =>
    simp only [isL2n] at hi
    obtain ⟨-, rfl⟩ := hi
    left
    rw [card_alternating_of_iso hm e]
    decide
  | sporadic s => simp [isL2n] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rcases r with _ | _ | r <;> simp [isL2n] at hi
      obtain ⟨hp, hn⟩ := hi
      right
      refine ⟨by have := q.exponent_pos; omega, ?_, ⟨⟨.A 1 q, hv⟩, by simp [hp], ⟨e⟩⟩⟩
      rw [hc.bridge ⟨.A 1 q, hv⟩ S ⟨e⟩]
      show orderA 1 q.card = _
      rw [TauCeti.PrimePower.card_def, hp, hn]
    | _ => simp [isL2n] at hi

theorem td4_data {S : Type} [Group S]
    (h : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [onLie] at hi
  | alternating m hm => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | trialityD4 q => exact ⟨q, hv, ⟨e⟩⟩
    | _ => simp [onLie] at hi

theorem card_le_of_ambiguous (hc : Ctx) {S : Type} [Group S] [Finite S] {j : TauCeti.CFSGIndex}
    (f : S ≃* j.Group) (hj : ambiguousChev 2 j) : Nat.card S ≤ 20160 := by
  cases j with
  | cyclic p hp => simp [ambiguousChev] at hj
  | alternating n hn =>
    have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by simpa [ambiguousChev] using hj
    rw [card_alternating_of_iso hn f]
    rcases hn' with rfl | rfl | rfl <;> decide
  | sporadic s => simp [ambiguousChev] at hj
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rcases r with _ | _ | r <;> simp [ambiguousChev] at hj
      · rw [hc.bridge ⟨.A 1 q, hv⟩ S ⟨f⟩]
        show orderA 1 q.card ≤ 20160
        rw [(TauCeti.PrimePower.card_def q).trans hj]
        decide
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r <;> simp [ambiguousChev] at hj
      · rw [hc.bridge ⟨.twistedA 2 q, hv⟩ S ⟨f⟩]
        show orderTwistedA 2 q.card ≤ 20160
        rw [(TauCeti.PrimePower.card_def q).trans hj]
        decide
    | _ => simp [ambiguousChev] at hj

theorem td4_chev2_even (hc : Ctx) {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) (hch : IsChevSimple 2 S) :
    q.p = 2 := by
  by_contra hq
  have hcard : Nat.card S = orderTrialityD4 q.card := hc.bridge ⟨.trialityD4 q, hv⟩ S ⟨e⟩
  rcases hch with ⟨j, hj, ⟨f⟩⟩ | ⟨j, hj, ⟨f⟩⟩
  · cases j with
    | cyclic p hp => simp [onLie] at hj
    | alternating m hm => simp [onLie] at hj
    | sporadic s => simp [onLie] at hj
    | lie idx => exact td4_odd_not_even hc q hv hq e idx (by simpa [onLie] using hj) f
  · have h1 := orderTrialityD4_gt (two_le_card q)
    have h2 := card_le_of_ambiguous hc f hj
    omega

theorem g2_chev2 (hc : Ctx) {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) (hch : IsChevSimple 2 S) : q.p = 2 := by
  by_contra hq
  have hcard : Nat.card S = orderG2 q.card := hc.bridge ⟨.G2 q, hv⟩ S ⟨e⟩
  have h3 : 3 ≤ q.card := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  rcases hch with ⟨j, hj, ⟨f⟩⟩ | ⟨j, hj, ⟨f⟩⟩
  · cases j with
    | cyclic p hp => simp [onLie] at hj
    | alternating m hm => simp [onLie] at hj
    | sporadic s => simp [onLie] at hj
    | lie idx => exact g2_odd_not_even hc q hv hq e idx (by simpa [onLie] using hj) f
  · have h1 := orderG2_ge h3
    have h2 := card_le_of_ambiguous hc f hj
    omega

theorem field_td4_ys09 (hc : Ctx) (S : Type) [Group S] [Finite S]
    (h1 : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False))
    (h2 : catalogIs S isYs09Type) : False := by
  obtain ⟨q, hv, ⟨e⟩⟩ := td4_data h1
  have hcard : Nat.card S = orderTrialityD4 q.card := hc.bridge ⟨.trialityD4 q, hv⟩ S ⟨e⟩
  have hne := td4_ne_ys09 (two_le_card q)
  obtain ⟨j, hj, hjS⟩ := h2
  rcases hj with h5 | h6 | h8 | hd
  · exact hne.1 (hcard.symm.trans (card_isU5two hc.bridge ⟨j, h5, hjS⟩))
  · exact hne.2.1 (hcard.symm.trans (card_isU6two hc.bridge ⟨j, h6, hjS⟩))
  · exact hne.2.2.1 (hcard.symm.trans (card_isSp8two hc.bridge ⟨j, h8, hjS⟩))
  · exact hne.2.2.2 (hcard.symm.trans (card_isD4two hc.bridge ⟨j, hd, hjS⟩))

theorem field_u42_a6 (hb : OrderBridge) (S : Type) [Group S] (h1 : catalogIs S S9.isU4two)
    (h2 : catalogIs S S10.isA6) : False := by
  obtain ⟨j, hj, ⟨f⟩⟩ := h2
  cases j with
  | cyclic p hp => simp [S10.isA6] at hj
  | alternating n hn =>
    simp only [S10.isA6] at hj
    subst hj
    haveI : Finite S := Finite.of_equiv _ f.symm.toEquiv
    have h360 := card_alternating_of_iso hn f
    have h4 := card_isU4two hb h1
    rw [h360] at h4
    revert h4
    decide
  | sporadic s => simp [S10.isA6] at hj
  | lie d => simp [S10.isA6] at hj

theorem field_u45_l2 (hc : Ctx) (S : Type) [Group S] [Finite S] (k : ℕ)
    (h1 : catalogIs S (fun i => S9.isU4two i ∨ S9.isU5two i)) (h2 : catalogIs S (isL2n k)) :
    False := by
  obtain ⟨i, hi, hiS⟩ := h1
  rcases data_isL2n hc h2 with h60 | ⟨hk, hcL, -⟩
  · rcases hi with h4 | h5
    · have := card_isU4two hc.bridge ⟨i, h4, hiS⟩; omega
    · have := card_isU5two hc.bridge ⟨i, h5, hiS⟩; omega
  · rcases hi with h4 | h5
    · exact u4_ne_L2 hk ((card_isU4two hc.bridge ⟨i, h4, hiS⟩).symm.trans hcL)
    · exact u5_ne_L2 hk ((card_isU5two hc.bridge ⟨i, h5, hiS⟩).symm.trans hcL)

theorem field_td4_u6 (hc : Ctx) (S : Type) [Group S] [Finite S] (m : ℕ) (hm : Odd m)
    (h1 : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False))
    (h2 : catalogIs S (isU6n m)) : False := by
  obtain ⟨q, hv, ⟨e⟩⟩ := td4_data h1
  obtain ⟨hm1, hc6, d, hd, ⟨f⟩⟩ := data_isU6n hc h2
  have hcard : Nat.card S = orderTrialityD4 q.card := hc.bridge ⟨.trialityD4 q, hv⟩ S ⟨e⟩
  by_cases hq : q.p = 2
  · have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
    rw [hqc] at hcard
    exact td4_ne_U6 q.exponent_pos hm1 hm (hcard.symm.trans hc6)
  · exact td4_odd_not_even hc q hv hq e d hd f

theorem field_td4_l2 (hc : Ctx) (S : Type) [Group S] [Finite S] (k : ℕ)
    (h1 : catalogIs S (isL2n k))
    (h2 : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) : False := by
  obtain ⟨q, hv, ⟨e⟩⟩ := td4_data h2
  have hcard : Nat.card S = orderTrialityD4 q.card := hc.bridge ⟨.trialityD4 q, hv⟩ S ⟨e⟩
  rcases data_isL2n hc h1 with h60 | ⟨hk, hcL, d, hd, ⟨f⟩⟩
  · have := orderTrialityD4_gt (two_le_card q)
    omega
  · by_cases hq : q.p = 2
    · have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
      rw [hqc] at hcard
      exact td4_ne_L2 q.exponent_pos hk (hcard.symm.trans hcL)
    · exact td4_odd_not_even hc q hv hq e d hd f

theorem field_g2_inj (hc : Ctx) (S : Type) [Group S] [Finite S] (n n' : ℕ)
    (h1 : catalogIs S (isG2n n)) (h2 : catalogIs S (isG2n n')) : n = n' := by
  obtain ⟨hn, hc1, -⟩ := data_isG2n hc h1
  obtain ⟨hn', hc2, -⟩ := data_isG2n hc h2
  exact g2_inj_arith hn hn' (hc1.symm.trans hc2)

theorem field_g2_u6 (hc : Ctx) (S : Type) [Group S] [Finite S] (n m : ℕ) (hnm : n = m ∨ Odd m)
    (h1 : catalogIs S (isG2n n)) (h2 : catalogIs S (isU6n m)) : False := by
  obtain ⟨hn, hc1, -⟩ := data_isG2n hc h1
  obtain ⟨hm, hc2, -⟩ := data_isU6n hc h2
  exact g2_ne_U6 hn hm hnm (hc1.symm.trans hc2)

theorem field_urn_l2 (hc : Ctx) (S : Type) [Group S] [Finite S] (n k : ℕ) (hodd : Odd n)
    (hn1 : 1 < n) (h1 : catalogIs S (isUrn n)) (h2 : catalogIs S (isL2n k)) : False := by
  obtain ⟨r, hr, hn, hc1⟩ := data_isUrn hc h1
  have hn3 : 3 ≤ n := by obtain ⟨c, hc'⟩ := hodd; omega
  rcases data_isL2n hc h2 with h60 | ⟨hk, hc2, -⟩
  · exact urn_ne_60 hr hn3 (hc1.symm.trans h60)
  · exact urn_ne_L2 hr hn3 hk (hc1.symm.trans hc2)

theorem field_u33_u6 (hc : Ctx) (S : Type) [Group S] [Finite S] (m : ℕ)
    (h1 : catalogIs S isU33) (h2 : catalogIs S (isU6n m)) : False := by
  obtain ⟨hm, hc2, -⟩ := data_isU6n hc h2
  exact u33_ne_U6 hm ((card_isU33 hc.bridge h1).symm.trans hc2)

theorem field_g2_chev2 (hc : Ctx) (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (h : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)) (hch : IsChevSimple 2 S) :
    q.p = 2 := by
  obtain ⟨e⟩ := h
  exact g2_chev2 hc q hv e hch

theorem field_u33_center (hc : Ctx) (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq3 : q.card = 3)
    (h : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)) :
    Subgroup.center S = ⊥ := by
  obtain ⟨e⟩ := h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative S := Subgroup.center_eq_top_iff.1 h
    have hprime : (Nat.card S).Prime := Group.is_simple_iff_prime_card.1 inferInstance
    have hcard : Nat.card S = 6048 := by
      rw [hc.bridge ⟨.twistedA 2 q, hv⟩ S ⟨e⟩]
      show orderTwistedA 2 q.card = 6048
      rw [hq3]
      decide
    rw [hcard] at hprime
    exact absurd hprime (by norm_num)

theorem field_td4_exc (hc : Ctx) (S : Type) [Group S] [Finite S] (hch : IsChevSimple 2 S)
    (h1 : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False))
    (h2 : catalogIs S excIndex) : False := by
  obtain ⟨q, hv, ⟨e⟩⟩ := td4_data h1
  have hq2 : q.p = 2 := td4_chev2_even hc q hv e hch
  have hcard : Nat.card S = orderTrialityD4 q.card := hc.bridge ⟨.trialityD4 q, hv⟩ S ⟨e⟩
  have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have hbig : 1048576 ≤ Nat.card S := hcard ▸ orderTrialityD4_gt (two_le_card q)
  have hcharq : (TauCeti.LieTypeIndex.trialityD4 q).characteristic = 2 := by simp [hq2]
  obtain ⟨i, hi, ⟨f⟩⟩ := h2
  cases i with
  | cyclic p hp => simp [excIndex] at hi
  | alternating n hn =>
    simp only [excIndex] at hi
    rw [card_alternating_of_iso hn f] at hbig
    rcases hi with rfl | rfl <;> revert hbig <;> decide
  | sporadic s =>
    simp only [excIndex] at hi
    subst hi
    have : Nat.card S = 443520 := by rw [Nat.card_congr f.toEquiv]; exact hc.m22
    omega
  | lie idx =>
    obtain ⟨d, hv'⟩ := idx
    cases d with
    | A r q' =>
      rcases r with _ | _ | _ | r <;> simp [excIndex] at hi
      by_cases hq' : q'.p = 2
      · have hcard' : Nat.card S = orderA 2 q'.card := hc.bridge ⟨.A 2 q', hv'⟩ S ⟨f⟩
        have hqc' : q'.card = 2 ^ q'.exponent := by rw [TauCeti.PrimePower.card_def, hq']
        rw [hqc'] at hcard'
        rw [hqc] at hcard
        exact td4_ne_A2 q.exponent_pos q'.exponent_pos (hcard.symm.trans hcard')
      · have hadm' : StatedLieAdmissible .PSL 3 q'.p q'.exponent :=
          ⟨q'.prime_p, q'.exponent_pos, by norm_num, by simp, by simp⟩
        refine xc hc (t' := .PSL) (n' := 3) (by simp) hadm' hq' ?_ ⟨.trialityD4 q, hv⟩ hcharq e
        refine hM'_of_card hadm' ?_
        rw [hc.bridge ⟨.A 2 q', hv'⟩ S ⟨f⟩]
        simp [lieOrderFormula, orderA, lieOrderNumerator, lieOrderDivisor,
          TauCeti.PrimePower.card_def]
    | twistedA r q' =>
      rcases r with _ | _ | _ | r <;> simp [excIndex] at hi
      by_cases hq' : q'.p = 2
      · have hcard' : Nat.card S = orderTwistedA 2 q'.card := hc.bridge ⟨.twistedA 2 q', hv'⟩ S ⟨f⟩
        have hqc' : q'.card = 2 ^ q'.exponent := by rw [TauCeti.PrimePower.card_def, hq']
        rw [hqc'] at hcard'
        rw [hqc] at hcard
        exact td4_ne_U3 q.exponent_pos q'.exponent_pos (hcard.symm.trans hcard')
      · have h3 : 3 ≤ q'.card :=
          ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
            ((TauCeti.LieTypeIndex.valid_iff _).mp hv').1).2 rfl
        have hadm' : StatedLieAdmissible .PSU 3 q'.p q'.exponent := by
          refine ⟨q'.prime_p, q'.exponent_pos, le_rfl, ?_⟩
          intro hh
          have : q'.p ^ q'.exponent = 2 := (Prod.mk.inj hh).2
          have h3' : 3 ≤ q'.p ^ q'.exponent := by rwa [TauCeti.PrimePower.card_def] at h3
          omega
        refine xc hc (t' := .PSU) (n' := 3) (by simp) hadm' hq' ?_ ⟨.trialityD4 q, hv⟩ hcharq e
        refine hM'_of_card hadm' ?_
        rw [hc.bridge ⟨.twistedA 2 q', hv'⟩ S ⟨f⟩]
        simp [lieOrderFormula, orderTwistedA, lieOrderNumerator, lieOrderDivisor,
          TauCeti.PrimePower.card_def]
    | _ => simp [excIndex] at hi

end CatDistinct

theorem catDistinctAt_of (hc : CatDistinct.Ctx) : CatDistinctAt where
  td4_ys09 := fun S _ _ h1 h2 => CatDistinct.field_td4_ys09 hc S h1 h2
  u42_a6 := fun S _ h1 h2 => CatDistinct.field_u42_a6 hc.bridge S h1 h2
  u45_l2 := fun S _ _ k h1 h2 => CatDistinct.field_u45_l2 hc S k h1 h2
  td4_u6 := fun S _ _ m hm h1 h2 => CatDistinct.field_td4_u6 hc S m hm h1 h2
  td4_l2 := fun S _ _ k h1 h2 => CatDistinct.field_td4_l2 hc S k h1 h2
  g2_inj := fun S _ _ n n' h1 h2 => CatDistinct.field_g2_inj hc S n n' h1 h2
  g2_u6 := fun S _ _ n m hnm h1 h2 => CatDistinct.field_g2_u6 hc S n m hnm h1 h2
  urn_l2 := fun S _ _ n k hodd hn1 h1 h2 => CatDistinct.field_urn_l2 hc S n k hodd hn1 h1 h2
  u33_u6 := fun S _ _ m h1 h2 => CatDistinct.field_u33_u6 hc S m h1 h2
  td4_exc := fun S _ _ hch h1 h2 => CatDistinct.field_td4_exc hc S hch h1 h2
  g2_chev2 := fun S _ _ q hv h hch => CatDistinct.field_g2_chev2 hc S q hv h hch
  u33_center := fun S _ _ _ q hv hq3 h => CatDistinct.field_u33_center hc S q hv hq3 h












