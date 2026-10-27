module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.SeitzReduction.RankOne.LieOdd

structure TwoPartBound (x L B : ℕ) : Prop where
  ne_zero : x ≠ 0
  le : L ≤ x
  ordProj_le : ordProj[2] x ≤ B

theorem TwoPartBound.mul {x y L L' B B' : ℕ} (hx : TwoPartBound x L B)
    (hy : TwoPartBound y L' B') : TwoPartBound (x * y) (L * L') (B * B') where
  ne_zero := mul_ne_zero hx.ne_zero hy.ne_zero
  le := Nat.mul_le_mul hx.le hy.le
  ordProj_le := by
    rw [Nat.ordProj_mul 2 hx.ne_zero hy.ne_zero]
    exact Nat.mul_le_mul hx.ordProj_le hy.ordProj_le

theorem TwoPartBound.mono {x L L' B B' : ℕ} (h : TwoPartBound x L B) (hL : L' ≤ L)
    (hB : B ≤ B') : TwoPartBound x L' B' :=
  ⟨h.ne_zero, hL.trans h.le, h.ordProj_le.trans hB⟩

theorem twoPartBound_one : TwoPartBound 1 1 1 := ⟨one_ne_zero, le_rfl, by simp⟩

theorem ordProj_two_of_odd {u : ℕ} (hu : Odd u) : ordProj[2] u = 1 := by
  rw [Nat.factorization_eq_zero_of_not_dvd
    (fun h => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)), pow_zero]

theorem ordProj_two_mul_odd {x u : ℕ} (hx : x ≠ 0) (hu : Odd u) :
    ordProj[2] (x * u) = ordProj[2] x := by
  rw [Nat.ordProj_mul 2 hx (by rintro rfl; exact (by decide : ¬ Odd 0) hu),
    ordProj_two_of_odd hu, mul_one]

theorem ordProj_two_pow_mul_odd {s u : ℕ} (hu : Odd u) : ordProj[2] (2 ^ s * u) = 2 ^ s := by
  rw [ordProj_two_mul_odd (pow_ne_zero _ two_ne_zero) hu,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

theorem ordProj_two_eq_two {x : ℕ} (hx : x % 4 = 2) : ordProj[2] x = 2 := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, Odd u ∧ x = 2 ^ 1 * u :=
    ⟨x / 2, Nat.odd_iff.mpr (by omega), by omega⟩
  rw [ordProj_two_pow_mul_odd hu, pow_one]

theorem exists_odd_pow_eq_mul_add_one (c b : ℕ) :
    ∃ S, Odd S ∧ (2 * c + 1) ^ (2 * b + 1) = 2 * c * S + 1 := by
  induction b with
  | zero => exact ⟨1, odd_one, by ring⟩
  | succ b ih =>
    obtain ⟨S, hS, hSe⟩ := ih
    refine ⟨(2 * c + 1) ^ 2 * S + (2 * c + 2),
      ((odd_two_mul_add_one c).pow.mul hS).add_even ⟨c + 1, by ring⟩, ?_⟩
    calc (2 * c + 1) ^ (2 * (b + 1) + 1) = (2 * c + 1) ^ 2 * (2 * c + 1) ^ (2 * b + 1) := by
          ring
      _ = 2 * c * ((2 * c + 1) ^ 2 * S + (2 * c + 2)) + 1 := by rw [hSe]; ring

theorem exists_odd_pow_add_one_eq_mul (c b : ℕ) :
    ∃ S, Odd S ∧ (2 * c + 1) ^ (2 * b + 1) + 1 = (2 * c + 2) * S := by
  induction b with
  | zero => exact ⟨1, odd_one, by ring⟩
  | succ b ih =>
    obtain ⟨S, hS, hSe⟩ := ih
    have hle : 2 * c ≤ (2 * c + 1) ^ 2 * S :=
      calc 2 * c ≤ (2 * c + 1) ^ 2 := by nlinarith
        _ ≤ (2 * c + 1) ^ 2 * S := Nat.le_mul_of_pos_right _ hS.pos
    refine ⟨(2 * c + 1) ^ 2 * S - 2 * c,
      Nat.Odd.sub_even hle ((odd_two_mul_add_one c).pow.mul hS) (even_two_mul c), ?_⟩
    zify [hle] at hSe ⊢
    linear_combination (2 * (c : ℤ) + 1) ^ 2 * hSe

theorem odd_pow_two_mul_mod_four (c b : ℕ) : (2 * c + 1) ^ (2 * b) % 4 = 1 := by
  have h : (2 * c + 1) ^ 2 % 4 = 1 := by
    have : (2 * c + 1) ^ 2 = 4 * (c ^ 2 + c) + 1 := by ring
    omega
  rw [pow_mul, Nat.pow_mod, h, one_pow]
  norm_num

theorem ordProj_pow_odd_sub_one {q u : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (hu : Odd u) :
    ordProj[2] (q ^ u - 1) = ordProj[2] (q - 1) := by
  obtain ⟨c, rfl⟩ := hqodd
  obtain ⟨b, rfl⟩ := hu
  obtain ⟨S, hS, hSe⟩ := exists_odd_pow_eq_mul_add_one c b
  rw [hSe, Nat.add_sub_cancel, show 2 * c + 1 - 1 = 2 * c by omega]
  exact ordProj_two_mul_odd (by omega) hS

theorem ordProj_pow_odd_add_one {q u : ℕ} (hqodd : Odd q) (hu : Odd u) :
    ordProj[2] (q ^ u + 1) = ordProj[2] (q + 1) := by
  obtain ⟨c, rfl⟩ := hqodd
  obtain ⟨b, rfl⟩ := hu
  obtain ⟨S, hS, hSe⟩ := exists_odd_pow_add_one_eq_mul c b
  rw [hSe, show 2 * c + 1 + 1 = 2 * c + 2 by ring]
  exact ordProj_two_mul_odd (by omega) hS

theorem ordProj_pow_even_add_one {q a : ℕ} (hqodd : Odd q) (ha : Even a) :
    ordProj[2] (q ^ a + 1) = 2 := by
  obtain ⟨c, rfl⟩ := hqodd
  obtain ⟨b, rfl⟩ := ha
  apply ordProj_two_eq_two
  have := odd_pow_two_mul_mod_four c b
  rw [show b + b = 2 * b by ring]
  omega

theorem ordProj_sub_one_mul_ordProj_add_one_le {q : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) :
    ordProj[2] (q - 1) * ordProj[2] (q + 1) ≤ 2 * (q + 1) := by
  obtain ⟨c, rfl⟩ := hqodd
  rw [show 2 * c + 1 - 1 = 2 * c by omega, show 2 * c + 1 + 1 = 2 * c + 2 by ring]
  rcases Nat.even_or_odd c with hce | hco
  · have h1 : ordProj[2] (2 * c + 2) = 2 := by
      rw [show 2 * c + 2 = 2 ^ 1 * (c + 1) by ring, ordProj_two_pow_mul_odd hce.add_one,
        pow_one]
    rw [h1]
    have := Nat.ordProj_le 2 (show 2 * c ≠ 0 by omega)
    omega
  · have h1 : ordProj[2] (2 * c) = 2 := by
      rw [show 2 * c = 2 ^ 1 * c by ring, ordProj_two_pow_mul_odd hco, pow_one]
    rw [h1]
    have := Nat.ordProj_le 2 (show 2 * c + 2 ≠ 0 by omega)
    omega

theorem pow_two_mul_sub_one_eq (q x : ℕ) : q ^ (2 * x) - 1 = (q ^ x - 1) * (q ^ x + 1) := by
  have h := Nat.sq_sub_sq (q ^ x) 1
  rw [one_pow] at h
  rw [show q ^ (2 * x) = (q ^ x) ^ 2 by ring, h, mul_comm]

theorem ordProj_pow_two_pow_mul_sub_one_le {q u : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (hu : Odd u)
    (s : ℕ) : ordProj[2] (q ^ (2 ^ s * u) - 1) ≤ (q + 1) * 2 ^ s := by
  have hu1 : 1 ≤ u := hu.pos
  have hne : ∀ x, 1 ≤ x → q ^ x - 1 ≠ 0 := fun x hx => by
    have : 3 ≤ q ^ x := le_trans hq (Nat.le_self_pow (by omega) q)
    omega
  induction s with
  | zero =>
    rw [pow_zero, one_mul, ordProj_pow_odd_sub_one hq hqodd hu, mul_one]
    exact (Nat.ordProj_le 2 (by omega)).trans (by omega)
  | succ s ih =>
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [show 2 ^ (0 + 1) * u = 2 * u by ring, pow_two_mul_sub_one_eq,
        Nat.ordProj_mul 2 (hne u hu1) (by omega), ordProj_pow_odd_sub_one hq hqodd hu,
        ordProj_pow_odd_add_one hqodd hu]
      have := ordProj_sub_one_mul_ordProj_add_one_le hq hqodd
      calc _ ≤ 2 * (q + 1) := this
        _ = (q + 1) * 2 ^ (0 + 1) := by ring
    · have hpos : 1 ≤ 2 ^ s * u := Nat.mul_pos (by positivity) hu1
      have heven : Even (2 ^ s * u) :=
        (Nat.even_pow.mpr ⟨even_two, hs.ne'⟩).mul_right u
      rw [show 2 ^ (s + 1) * u = 2 * (2 ^ s * u) by ring, pow_two_mul_sub_one_eq,
        Nat.ordProj_mul 2 (hne _ hpos) (by omega), ordProj_pow_even_add_one hqodd heven]
      calc _ ≤ (q + 1) * 2 ^ s * 2 := Nat.mul_le_mul_right 2 ih
        _ = (q + 1) * 2 ^ (s + 1) := by ring

theorem ordProj_pow_add_one_le {q : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (a : ℕ) :
    ordProj[2] (q ^ a + 1) ≤ q + 1 := by
  rcases Nat.even_or_odd a with hae | hao
  · rw [ordProj_pow_even_add_one hqodd hae]
    omega
  · rw [ordProj_pow_odd_add_one hqodd hao]
    exact Nat.ordProj_le 2 (by omega)

theorem pow_pred_mul_sub_one_le_pow_sub_one {q a : ℕ} (hq : 1 ≤ q) (ha : 1 ≤ a) :
    q ^ (a - 1) * (q - 1) ≤ q ^ a - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, Nat.mul_sub_one]
  have := Nat.one_le_pow k q hq
  omega

theorem pow_pred_mul_sub_one_le_pow_add_one {q a : ℕ} (ha : 1 ≤ a) :
    q ^ (a - 1) * (q - 1) ≤ q ^ a + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  have : q ^ k * (q - 1) ≤ q ^ k * q := Nat.mul_le_mul_left _ (Nat.sub_le q 1)
  omega

theorem twoPartBound_pow_sub_one {q a s u : ℕ} (hq : 3 ≤ q) (hqodd : Odd q)
    (ha : a = 2 ^ s * u) (hu : Odd u) :
    TwoPartBound (q ^ a - 1) (q ^ (a - 1) * (q - 1)) ((q + 1) * 2 ^ s) := by
  have ha1 : 1 ≤ a := ha ▸ Nat.mul_pos (by positivity) hu.pos
  refine ⟨?_, pow_pred_mul_sub_one_le_pow_sub_one (by omega) ha1, ?_⟩
  · have : 3 ≤ q ^ a := le_trans hq (Nat.le_self_pow (by omega) q)
    omega
  · rw [ha]
    exact ordProj_pow_two_pow_mul_sub_one_le hq hqodd hu s

theorem twoPartBound_pow_sub_one' {q a : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (ha : 1 ≤ a) :
    TwoPartBound (q ^ a - 1) (q ^ (a - 1) * (q - 1)) ((q + 1) * ordProj[2] a) := by
  obtain ⟨s, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show a ≠ 0 by omega)
  rw [ordProj_two_pow_mul_odd hu]
  exact twoPartBound_pow_sub_one hq hqodd rfl hu

theorem twoPartBound_pow_add_one {q a : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (ha : 1 ≤ a) :
    TwoPartBound (q ^ a + 1) (q ^ (a - 1) * (q - 1)) (q + 1) :=
  ⟨by omega, pow_pred_mul_sub_one_le_pow_add_one ha, ordProj_pow_add_one_le hq hqodd a⟩

theorem three_mul_sq_le {q : ℕ} (hq : 3 ≤ q) : 3 * (q + 1) ^ 2 ≤ 8 * q * (q - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 3 := ⟨q - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega]
  nlinarith

theorem lt_of_twoPartBound {q N N' r w G g e h cof M : ℕ} (hq : 3 ≤ q) (hqodd : Odd q)
    (heq : q ^ N * cof = 2 ^ e * h * g)
    (hb : TwoPartBound cof (q ^ N' * (q - 1) ^ r) ((q + 1) ^ r * 2 ^ w))
    (hg : g ≤ G) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) (hM : N + N' = r + 1 + M) :
    3 ^ r * q ^ M < 8 ^ r * 4 ^ w * (r + w) * G := by
  have hcop : Nat.Coprime (2 ^ e) (q ^ N) := (Nat.coprime_two_left.mpr hqodd).pow e N
  have hdvd : 2 ^ e ∣ cof := by
    have : 2 ^ e ∣ q ^ N * cof := by
      rw [heq]
      exact (dvd_mul_right _ _).mul_right _
    exact hcop.dvd_of_dvd_mul_left this
  have h2e : 2 ^ e ≤ (q + 1) ^ r * 2 ^ w :=
    (Nat.pow_le_pow_right two_pos
      ((Nat.prime_two.pow_dvd_iff_le_factorization hb.ne_zero).mp hdvd)).trans hb.ordProj_le
  have he : e ≤ q * r + w := by
    have : (q + 1) ^ r * 2 ^ w ≤ 2 ^ (q * r + w) := by
      rw [pow_add, pow_mul]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left Nat.lt_two_pow_self r)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (h2e.trans this)
  have h2 : 2 ≤ 2 ^ e :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he1
  have hh : h ≤ (2 ^ e - 1) * e := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdiv
  have hcof : q ^ N' * (q - 1) ^ r ≤ cof := hb.le
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · rw [mul_zero] at heq
      exact absurd heq (mul_ne_zero (by positivity) hb.ne_zero)
    · exact hg0
  have hG : 0 < G := by omega
  have h38 := three_mul_sq_le hq
  have hqrw : q * r + w ≤ q * (r + w) := by
    rw [mul_add]
    have : w ≤ q * w := Nat.le_mul_of_pos_left w (by omega)
    omega
  have h4 : (2 : ℕ) ^ w * 2 ^ w = 4 ^ w := by
    rw [← mul_pow]
    norm_num
  have hstrict : 2 ^ e * ((2 ^ e - 1) * e) * G < 2 ^ e * 2 ^ e * e * G := by
    have h1 : (2 ^ e - 1) * e < 2 ^ e * e := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have h3 : 2 ^ e * ((2 ^ e - 1) * e) < 2 ^ e * (2 ^ e * e) :=
      Nat.mul_lt_mul_of_pos_left h1 (by positivity)
    calc 2 ^ e * ((2 ^ e - 1) * e) * G < 2 ^ e * (2 ^ e * e) * G :=
          Nat.mul_lt_mul_of_pos_right h3 hG
      _ = 2 ^ e * 2 ^ e * e * G := by ring
  have key : 3 ^ r * q ^ M * (q ^ (r + 1) * (q - 1) ^ r) <
      8 ^ r * 4 ^ w * (r + w) * G * (q ^ (r + 1) * (q - 1) ^ r) := by
    calc 3 ^ r * q ^ M * (q ^ (r + 1) * (q - 1) ^ r)
          = 3 ^ r * (q ^ (N + N') * (q - 1) ^ r) := by rw [hM]; ring
      _ = 3 ^ r * (q ^ N * (q ^ N' * (q - 1) ^ r)) := by ring
      _ ≤ 3 ^ r * (q ^ N * cof) := by gcongr
      _ = 3 ^ r * (2 ^ e * h * g) := by rw [heq]
      _ ≤ 3 ^ r * (2 ^ e * ((2 ^ e - 1) * e) * G) := by gcongr
      _ < 3 ^ r * (2 ^ e * 2 ^ e * e * G) := Nat.mul_lt_mul_of_pos_left hstrict (by positivity)
      _ ≤ 3 ^ r * (((q + 1) ^ r * 2 ^ w) * ((q + 1) ^ r * 2 ^ w) * (q * r + w) * G) := by
          gcongr
      _ = (3 * (q + 1) ^ 2) ^ r * 4 ^ w * (q * r + w) * G := by
          rw [mul_pow, pow_right_comm, sq, ← h4]
          ring
      _ ≤ (8 * q * (q - 1)) ^ r * 4 ^ w * (q * (r + w)) * G := by gcongr
      _ = 8 ^ r * 4 ^ w * (r + w) * G * (q ^ (r + 1) * (q - 1) ^ r) := by
          rw [mul_pow, mul_pow]
          ring
  exact Nat.lt_of_mul_lt_mul_right key

theorem false_of_two_pow_mul_eq {c E e h : ℕ} (hc : 2 ^ e * h = c) (hE : ¬ 2 ^ (E + 1) ∣ c)
    (hlt : 2 ^ E * (2 ^ E - 1) * E < c) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have heE : e ≤ E := by
    by_contra hlt'
    apply hE
    rw [← hc]
    exact (pow_dvd_pow 2 (by omega)).mul_right h
  have h2 : 2 ≤ 2 ^ e :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he1
  have hh : h ≤ (2 ^ e - 1) * e := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdiv
  have h1 : 2 ^ e ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) heE
  have : c ≤ 2 ^ E * (2 ^ E - 1) * E := by
    rw [← hc]
    calc 2 ^ e * h ≤ 2 ^ e * ((2 ^ e - 1) * e) := Nat.mul_le_mul_left _ hh
      _ = 2 ^ e * (2 ^ e - 1) * e := by ring
      _ ≤ 2 ^ E * (2 ^ E - 1) * E := Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) heE
  omega

end CFSG.SeitzReduction.RankOne.LieOdd
