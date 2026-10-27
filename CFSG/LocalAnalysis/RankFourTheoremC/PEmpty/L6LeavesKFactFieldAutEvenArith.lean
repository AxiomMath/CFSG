module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

@[expose] def V2Le (a b : ℕ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a.factorization 2 ≤ b.factorization 2

theorem V2Le.mul {a b a' b' : ℕ} (h : V2Le a a') (h' : V2Le b b') : V2Le (a * b) (a' * b') := by
  obtain ⟨ha, ha', hle⟩ := h
  obtain ⟨hb, hb', hle'⟩ := h'
  refine ⟨mul_ne_zero ha hb, mul_ne_zero ha' hb', ?_⟩
  rw [Nat.factorization_mul ha hb, Nat.factorization_mul ha' hb']
  simp only [Finsupp.add_apply]
  omega

theorem V2Le.one : V2Le 1 1 := ⟨one_ne_zero, one_ne_zero, le_rfl⟩

theorem V2Le.prod {ι : Type*} {s : Finset ι} {f g : ι → ℕ} (h : ∀ i ∈ s, V2Le (f i) (g i)) :
    V2Le (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using V2Le.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem V2Le.rfl' {a : ℕ} (ha : a ≠ 0) : V2Le a a := ⟨ha, ha, le_rfl⟩

theorem factorization_two_of_odd {a : ℕ} (ha : Odd a) : a.factorization 2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  rw [← even_iff_two_dvd]
  exact Nat.not_even_iff_odd.mpr ha

theorem V2Le.of_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) : V2Le a b := by
  refine ⟨ha.pos.ne', hb.pos.ne', ?_⟩
  rw [factorization_two_of_odd ha]
  exact Nat.zero_le _

theorem odd_geomSum {y p : ℕ} (hy : Odd y) (hp : Odd p) : Odd (∑ k ∈ Finset.range p, y ^ k) := by
  rw [Finset.odd_sum_iff_odd_card_odd]
  have : (Finset.range p).filter (fun k => Odd (y ^ k)) = Finset.range p := by
    apply Finset.filter_true_of_mem
    intro k _
    exact hy.pow
  rw [this, Finset.card_range]
  exact hp

theorem factorization_two_pow_sub_one {y p : ℕ} (hy : Odd y) (hy3 : 3 ≤ y) (hp : Odd p) :
    (y ^ p - 1).factorization 2 = (y - 1).factorization 2 := by
  have hy2 : 2 ≤ y := by omega
  have hdvd : y - 1 ∣ y ^ p - 1 := Nat.sub_one_dvd_pow_sub_one y p
  have hgs : ∑ k ∈ Finset.range p, y ^ k = (y ^ p - 1) / (y - 1) := Nat.geomSum_eq hy2 p
  have hmul : (y - 1) * ∑ k ∈ Finset.range p, y ^ k = y ^ p - 1 := by
    rw [hgs]
    exact Nat.mul_div_cancel' hdvd
  have hS := odd_geomSum hy hp
  have hy1 : y - 1 ≠ 0 := by omega
  rw [← hmul, Nat.factorization_mul hy1 hS.pos.ne']
  simp [factorization_two_of_odd hS]

theorem three_le_pow {y p : ℕ} (hy3 : 3 ≤ y) (hp : 1 ≤ p) : 3 ≤ y ^ p :=
  calc 3 ≤ y := hy3
    _ = y ^ 1 := (pow_one y).symm
    _ ≤ y ^ p := Nat.pow_le_pow_right (by omega) hp

theorem factorization_two_pow_add_one {y p : ℕ} (hy : Odd y) (hy3 : 3 ≤ y) (hp : Odd p) :
    (y ^ p + 1).factorization 2 = (y + 1).factorization 2 := by
  have key : ∀ A : ℕ, 1 ≤ A → (A - 1) * (A + 1) = A * A - 1 := by
    intro A hA
    obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (B + 1) * (B + 1) = B * (B + 1 + 1) + 1 := by ring
    omega
  have hyp3 : 3 ≤ y ^ p := three_le_pow hy3 hp.pos
  have hy2' : 3 ≤ y ^ 2 := three_le_pow hy3 (by norm_num)
  have e : (y ^ 2) ^ p = y ^ p * y ^ p := by rw [← pow_mul, mul_comm, pow_mul, sq]
  have h1 : (y ^ p - 1) * (y ^ p + 1) = (y ^ 2) ^ p - 1 := by rw [e]; exact key _ (by omega)
  have h2 : (y - 1) * (y + 1) = y ^ 2 - 1 := by rw [sq]; exact key _ (by omega)
  have hv1 := factorization_two_pow_sub_one hy hy3 hp
  have hv2 := factorization_two_pow_sub_one (hy.pow (n := 2)) hy2' hp
  have n1 : y ^ p - 1 ≠ 0 := by omega
  have n2 : y ^ p + 1 ≠ 0 := by omega
  have n3 : y - 1 ≠ 0 := by omega
  have n4 : y + 1 ≠ 0 := by omega
  have f1 := congrArg (fun m => m.factorization 2) h1
  have f2 := congrArg (fun m => m.factorization 2) h2
  simp only [Nat.factorization_mul n1 n2, Nat.factorization_mul n3 n4, Finsupp.add_apply] at f1 f2
  omega

variable {x p : ℕ}

theorem V2Le.pow_sub_one (hx : Odd x) (hx3 : 3 ≤ x) (hp : Odd p) {k : ℕ} (hk : 1 ≤ k) :
    V2Le ((x ^ p) ^ k - 1) (x ^ k - 1) := by
  have hy3 : 3 ≤ x ^ k := three_le_pow hx3 hk
  have e : (x ^ p) ^ k = (x ^ k) ^ p := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hz : 3 ≤ (x ^ k) ^ p := three_le_pow hy3 hp.pos
  rw [e]
  exact ⟨by omega, by omega, (factorization_two_pow_sub_one hx.pow hy3 hp).le⟩

theorem V2Le.pow_add_one (hx : Odd x) (hx3 : 3 ≤ x) (hp : Odd p) {k : ℕ} (hk : 1 ≤ k) :
    V2Le ((x ^ p) ^ k + 1) (x ^ k + 1) := by
  have hy3 : 3 ≤ x ^ k := three_le_pow hx3 hk
  have e : (x ^ p) ^ k = (x ^ k) ^ p := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e]
  exact ⟨by omega, by omega, (factorization_two_pow_add_one hx.pow hy3 hp).le⟩

theorem V2Le.pow_pow (hx : Odd x) (N : ℕ) : V2Le ((x ^ p) ^ N) (x ^ N) :=
  V2Le.of_odd hx.pow.pow hx.pow

theorem V2Le.tri (hx : Odd x) :
    V2Le ((x ^ p) ^ 8 + (x ^ p) ^ 4 + 1) (x ^ 8 + x ^ 4 + 1) :=
  V2Le.of_odd (hx.pow.pow.add_odd hx.pow.pow).add_one (hx.pow.add_odd hx.pow).add_one

theorem v2Le_numerator (t : StatedLieTag) (n : ℕ) (hx : Odd x) (hx3 : 3 ≤ x) (hp : Odd p)
    (hn : (t = .POmegaPlus ∨ t = .POmegaMinus) → 1 ≤ n) :
    V2Le (lieOrderNumerator t n (x ^ p)) (lieOrderNumerator t n x) := by
  have hs : ∀ {k : ℕ}, 1 ≤ k → V2Le ((x ^ p) ^ k - 1) (x ^ k - 1) :=
    fun hk => V2Le.pow_sub_one hx hx3 hp hk
  have ha : ∀ {k : ℕ}, 1 ≤ k → V2Le ((x ^ p) ^ k + 1) (x ^ k + 1) :=
    fun hk => V2Le.pow_add_one hx hx3 hp hk
  have h1 : V2Le (x ^ p - 1) (x - 1) := by simpa using hs (k := 1) le_rfl
  have h1' : V2Le (x ^ p + 1) (x + 1) := by simpa using ha (k := 1) le_rfl
  cases t with
  | PSL =>
    simp only [lieOrderNumerator]
    exact (V2Le.pow_pow hx _).mul (V2Le.prod fun i hi => hs (by simp at hi; omega))
  | PSU =>
    simp only [lieOrderNumerator]
    refine (V2Le.pow_pow hx _).mul (V2Le.prod fun i hi => ?_)
    have hi2 : 1 ≤ i := by simp at hi; omega
    by_cases he : Even i
    · simpa [he] using hs hi2
    · simpa [he] using ha hi2
  | PSp =>
    simp only [lieOrderNumerator]
    exact (V2Le.pow_pow hx _).mul (V2Le.prod fun i hi => hs (by simp at hi; omega))
  | POmegaOdd =>
    simp only [lieOrderNumerator]
    exact (V2Le.pow_pow hx _).mul (V2Le.prod fun i hi => hs (by simp at hi; omega))
  | POmegaPlus =>
    simp only [lieOrderNumerator]
    exact ((V2Le.pow_pow hx _).mul (hs (hn (Or.inl rfl)))).mul
      (V2Le.prod fun i hi => hs (by simp at hi; omega))
  | POmegaMinus =>
    simp only [lieOrderNumerator]
    exact ((V2Le.pow_pow hx _).mul (ha (hn (Or.inr rfl)))).mul
      (V2Le.prod fun i hi => hs (by simp at hi; omega))
  | G2 =>
    simp only [lieOrderNumerator]
    exact ((V2Le.pow_pow hx _).mul (hs (k := 6) (by norm_num))).mul (hs (k := 2) (by norm_num))
  | F4 =>
    simp only [lieOrderNumerator]
    exact ((((V2Le.pow_pow hx _).mul (hs (k := 12) (by norm_num))).mul
      (hs (k := 8) (by norm_num))).mul (hs (k := 6) (by norm_num))).mul
      (hs (k := 2) (by norm_num))
  | E6 =>
    simp only [lieOrderNumerator]
    exact ((((((V2Le.pow_pow hx _).mul (hs (k := 12) (by norm_num))).mul
      (hs (k := 9) (by norm_num))).mul (hs (k := 8) (by norm_num))).mul
      (hs (k := 6) (by norm_num))).mul (hs (k := 5) (by norm_num))).mul
      (hs (k := 2) (by norm_num))
  | E7 =>
    simp only [lieOrderNumerator]
    exact (((((((V2Le.pow_pow hx _).mul (hs (k := 18) (by norm_num))).mul
      (hs (k := 14) (by norm_num))).mul (hs (k := 12) (by norm_num))).mul
      (hs (k := 10) (by norm_num))).mul (hs (k := 8) (by norm_num))).mul
      (hs (k := 6) (by norm_num))).mul (hs (k := 2) (by norm_num))
  | E8 =>
    simp only [lieOrderNumerator]
    exact ((((((((V2Le.pow_pow hx _).mul (hs (k := 30) (by norm_num))).mul
      (hs (k := 24) (by norm_num))).mul (hs (k := 20) (by norm_num))).mul
      (hs (k := 18) (by norm_num))).mul (hs (k := 14) (by norm_num))).mul
      (hs (k := 12) (by norm_num))).mul (hs (k := 8) (by norm_num))).mul
      (hs (k := 2) (by norm_num))
  | twistedE6 =>
    simp only [lieOrderNumerator]
    exact ((((((V2Le.pow_pow hx _).mul (hs (k := 12) (by norm_num))).mul
      (ha (k := 9) (by norm_num))).mul (hs (k := 8) (by norm_num))).mul
      (hs (k := 6) (by norm_num))).mul (ha (k := 5) (by norm_num))).mul
      (hs (k := 2) (by norm_num))
  | trialityD4 =>
    simp only [lieOrderNumerator]
    exact (((V2Le.pow_pow hx _).mul (V2Le.tri hx)).mul (hs (k := 6) (by norm_num))).mul
      (hs (k := 2) (by norm_num))
  | twistedB2 =>
    simp only [lieOrderNumerator]
    exact ((V2Le.pow_pow hx _).mul (ha (k := 2) (by norm_num))).mul h1
  | twistedG2 =>
    simp only [lieOrderNumerator]
    exact ((V2Le.pow_pow hx _).mul (ha (k := 3) (by norm_num))).mul h1
  | twistedF4 =>
    simp only [lieOrderNumerator]
    exact ((((V2Le.pow_pow hx _).mul (ha (k := 6) (by norm_num))).mul
      (hs (k := 4) (by norm_num))).mul (ha (k := 3) (by norm_num))).mul h1
  | Tits =>
    simp only [lieOrderNumerator]
    exact V2Le.rfl' (by norm_num)

theorem lieOrderDivisor_dvd_pow (t : StatedLieTag) (n x : ℕ) {p : ℕ} (hp : Odd p) :
    lieOrderDivisor t n x ∣ lieOrderDivisor t n (x ^ p) := by
  have hs : ∀ y : ℕ, y - 1 ∣ y ^ p - 1 := fun y => Nat.sub_one_dvd_pow_sub_one y p
  have ha : ∀ y : ℕ, y + 1 ∣ y ^ p + 1 := fun y => by
    simpa using Odd.nat_add_dvd_pow_add_pow y 1 hp
  have hq : ∀ k : ℕ, (x ^ p) ^ k = (x ^ k) ^ p := fun k => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  cases t with
  | PSL => exact Nat.gcd_dvd_gcd_of_dvd_right n (hs x)
  | PSU => exact Nat.gcd_dvd_gcd_of_dvd_right n (ha x)
  | PSp => exact Nat.gcd_dvd_gcd_of_dvd_right 2 (hs x)
  | POmegaOdd => exact dvd_rfl
  | POmegaPlus =>
    show Nat.gcd 4 (x ^ n - 1) ∣ Nat.gcd 4 ((x ^ p) ^ n - 1)
    rw [hq n]
    exact Nat.gcd_dvd_gcd_of_dvd_right 4 (hs (x ^ n))
  | POmegaMinus =>
    show Nat.gcd 4 (x ^ n + 1) ∣ Nat.gcd 4 ((x ^ p) ^ n + 1)
    rw [hq n]
    exact Nat.gcd_dvd_gcd_of_dvd_right 4 (ha (x ^ n))
  | E6 => exact Nat.gcd_dvd_gcd_of_dvd_right 3 (hs x)
  | E7 => exact Nat.gcd_dvd_gcd_of_dvd_right 2 (hs x)
  | twistedE6 => exact Nat.gcd_dvd_gcd_of_dvd_right 3 (ha x)
  | G2 | F4 | E8 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits => exact dvd_rfl

theorem lieOrderDivisor_ne_zero (t : StatedLieTag) (n x : ℕ) (hx : 2 ≤ x) :
    lieOrderDivisor t n x ≠ 0 := by
  cases t with
  | PSL => exact (Nat.gcd_pos_of_pos_right n (by omega : 0 < x - 1)).ne'
  | PSU => exact (Nat.gcd_pos_of_pos_right n (by omega : 0 < x + 1)).ne'
  | PSp => exact (Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 2)).ne'
  | POmegaOdd => exact two_ne_zero
  | POmegaPlus => exact (Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 4)).ne'
  | POmegaMinus => exact (Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 4)).ne'
  | E6 => exact (Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 3)).ne'
  | E7 => exact (Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 2)).ne'
  | twistedE6 => exact (Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 3)).ne'
  | G2 | F4 | E8 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits => exact one_ne_zero

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
