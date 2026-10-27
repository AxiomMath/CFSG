module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42LinkCheck
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoArr
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD42Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.AGLEmbedding.ChevOuter
  CFSG.RankThree.PartTwo.Sec4.Item434D42

namespace TD42

@[expose] def gf8Lit (l : Array ℕ) : Array GF8 := l.map GF8.ofNat'

@[expose] def U1 : Array ℕ :=
  #[1, 5, 5, 0, 0, 0, 0, 0,
    6, 2, 2, 0, 0, 0, 0, 0,
    7, 7, 6, 7, 3, 2, 2, 0,
    7, 7, 5, 4, 6, 7, 7, 0,
    7, 7, 3, 1, 6, 4, 4, 0,
    7, 7, 4, 6, 7, 5, 5, 0,
    0, 0, 4, 4, 4, 4, 5, 5,
    0, 0, 4, 4, 4, 4, 2, 2]

@[expose] def U2 : Array ℕ :=
  #[4, 2, 7, 6, 4, 1, 1, 0,
    4, 2, 0, 5, 6, 4, 4, 0,
    3, 3, 2, 2, 2, 1, 3, 1,
    3, 3, 3, 3, 1, 2, 5, 6,
    3, 3, 6, 3, 6, 0, 4, 2,
    3, 3, 7, 2, 5, 3, 6, 7,
    0, 0, 6, 6, 6, 6, 0, 6,
    0, 0, 6, 6, 6, 6, 3, 5]

@[expose] def U3 : Array ℕ :=
  #[2, 7, 6, 0, 6, 6, 7, 5,
    0, 5, 0, 7, 6, 7, 3, 2,
    0, 0, 5, 1, 2, 4, 1, 6,
    0, 0, 0, 4, 0, 6, 1, 0,
    0, 0, 0, 0, 7, 5, 6, 6,
    0, 0, 0, 0, 0, 2, 0, 6,
    0, 0, 0, 0, 0, 0, 2, 7,
    0, 0, 0, 0, 0, 0, 0, 5]

@[expose] def U6 : Array ℕ :=
  #[4, 3, 4, 5, 0, 5, 6, 2,
    0, 7, 0, 7, 7, 4, 7, 4,
    0, 0, 7, 1, 4, 6, 1, 5,
    0, 0, 0, 6, 0, 2, 6, 5,
    0, 0, 0, 0, 3, 7, 3, 0,
    0, 0, 0, 0, 0, 4, 0, 4,
    0, 0, 0, 0, 0, 0, 4, 3,
    0, 0, 0, 0, 0, 0, 0, 7]

@[expose] def U7 : Array ℕ :=
  #[4, 5, 2, 6, 4, 4, 5, 7,
    5, 4, 0, 4, 6, 7, 5, 5,
    1, 1, 5, 7, 3, 1, 3, 4,
    1, 1, 7, 5, 0, 2, 7, 2,
    1, 1, 3, 0, 5, 6, 5, 4,
    1, 1, 0, 3, 7, 4, 1, 3,
    0, 0, 1, 1, 1, 1, 4, 4,
    0, 0, 1, 1, 1, 1, 5, 5]

@[expose] def U9 : Array ℕ :=
  #[3, 5, 7, 4, 7, 3, 2, 7,
    0, 6, 0, 2, 7, 2, 4, 5,
    0, 0, 6, 3, 4, 2, 1, 3,
    0, 0, 0, 5, 0, 6, 1, 4,
    0, 0, 0, 0, 2, 1, 7, 7,
    0, 0, 0, 0, 0, 3, 0, 7,
    0, 0, 0, 0, 0, 0, 3, 5,
    0, 0, 0, 0, 0, 0, 0, 6]

@[expose] def U12 : Array ℕ :=
  #[6, 5, 7, 7, 4, 3, 5, 7,
    0, 3, 0, 7, 1, 1, 4, 2,
    0, 0, 3, 1, 6, 2, 2, 3,
    0, 0, 0, 2, 0, 4, 7, 7,
    0, 0, 0, 0, 5, 3, 2, 4,
    0, 0, 0, 0, 0, 6, 0, 7,
    0, 0, 0, 0, 0, 0, 6, 5,
    0, 0, 0, 0, 0, 0, 0, 3]

@[expose] def U15 : Array ℕ :=
  #[7, 3, 4, 0, 5, 5, 4, 2,
    0, 4, 0, 3, 6, 1, 7, 6,
    0, 0, 4, 7, 2, 6, 4, 5,
    0, 0, 0, 3, 0, 4, 7, 0,
    0, 0, 0, 0, 6, 1, 7, 5,
    0, 0, 0, 0, 0, 7, 0, 4,
    0, 0, 0, 0, 0, 0, 7, 3,
    0, 0, 0, 0, 0, 0, 0, 4]

@[expose] def U18 : Array ℕ :=
  #[5, 7, 6, 6, 0, 6, 2, 5,
    0, 2, 0, 6, 1, 1, 3, 7,
    0, 0, 2, 5, 6, 4, 7, 6,
    0, 0, 0, 7, 0, 2, 6, 6,
    0, 0, 0, 0, 4, 1, 7, 0,
    0, 0, 0, 0, 0, 5, 0, 6,
    0, 0, 0, 0, 0, 0, 5, 7,
    0, 0, 0, 0, 0, 0, 0, 2]

@[expose] def U21 : Array ℕ :=
  #[1, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def u0w : List ℕ := [9, 17, 15, 3, 8, 6, 16]

@[expose] def u0 : lineGroup := wordX u0w

@[expose] def s0 : lineGroup := u0 ^ 7

@[expose] def y0 : lineGroup := u0 ^ 3

set_option maxRecDepth 100000

theorem wordArr_u0w : wordArr u0w = gf8Lit U1 := by decide +kernel

theorem mat_u0 : (((u0 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U1) := by
  rw [u0, coe_wordX (by decide), coe_wordGL, wordArr_u0w]

theorem mat_mul_pow {a b c : ℕ} {A B C : Array ℕ}
    (ha : (((u0 ^ a : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat (gf8Lit A))
    (hb : (((u0 ^ b : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat (gf8Lit B))
    (hc : mulArr (gf8Lit A) (gf8Lit B) = gf8Lit C) (habc : a + b = c) :
    (((u0 ^ c : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat (gf8Lit C) := by
  rw [← habc, pow_add, Subgroup.coe_mul, Units.val_mul, ha, hb, ← toMat_mulArr, hc]

theorem mat_u1 : (((u0 ^ 1 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U1) := by rw [pow_one]; exact mat_u0

theorem mat_u2 : (((u0 ^ 2 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U2) :=
  mat_mul_pow mat_u1 mat_u1 (by decide +kernel) (by norm_num)

theorem mat_u3 : (((u0 ^ 3 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U3) :=
  mat_mul_pow mat_u2 mat_u1 (by decide +kernel) (by norm_num)

theorem mat_u6 : (((u0 ^ 6 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U6) :=
  mat_mul_pow mat_u3 mat_u3 (by decide +kernel) (by norm_num)

theorem mat_u7 : (((u0 ^ 7 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U7) :=
  mat_mul_pow mat_u6 mat_u1 (by decide +kernel) (by norm_num)

theorem mat_u9 : (((u0 ^ 9 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U9) :=
  mat_mul_pow mat_u6 mat_u3 (by decide +kernel) (by norm_num)

theorem mat_u12 : (((u0 ^ 12 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U12) :=
  mat_mul_pow mat_u6 mat_u6 (by decide +kernel) (by norm_num)

theorem mat_u15 : (((u0 ^ 15 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U15) :=
  mat_mul_pow mat_u12 mat_u3 (by decide +kernel) (by norm_num)

theorem mat_u18 : (((u0 ^ 18 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U18) :=
  mat_mul_pow mat_u12 mat_u6 (by decide +kernel) (by norm_num)

theorem mat_u21 : (((u0 ^ 21 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
    toMat (gf8Lit U21) :=
  mat_mul_pow mat_u18 mat_u3 (by decide +kernel) (by norm_num)

theorem matrix_one_of_toMat {A : Array ℕ} (h : toMat (gf8Lit A) = 1) :
    (((1 : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat (gf8Lit A) := by
  rw [h]
  rfl

theorem u0_pow_21 : u0 ^ 21 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [mat_u21]
  exact (matrix_one_of_toMat (by decide +kernel)).symm

theorem u0_pow_3_ne : u0 ^ 3 ≠ 1 := by
  intro h
  have := congrArg (fun g : lineGroup => (((g : lineGroup) : GL (Fin 8) GF8) :
    Matrix (Fin 8) (Fin 8) GF8)) h
  simp only [mat_u3] at this
  exact absurd (this.trans rfl) (by decide +kernel)

theorem u0_pow_7_ne : u0 ^ 7 ≠ 1 := by
  intro h
  have := congrArg (fun g : lineGroup => (((g : lineGroup) : GL (Fin 8) GF8) :
    Matrix (Fin 8) (Fin 8) GF8)) h
  simp only [mat_u7] at this
  exact absurd (this.trans rfl) (by decide +kernel)

local instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance factPrimeThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

theorem y0_pow_seven : y0 ^ 7 = 1 := by
  rw [y0, ← pow_mul]
  exact u0_pow_21

theorem orderOf_y0 : orderOf y0 = 7 := orderOf_eq_prime y0_pow_seven u0_pow_3_ne

theorem s0_pow_three : s0 ^ 3 = 1 := by
  rw [s0, ← pow_mul]
  exact u0_pow_21

theorem orderOf_s0 : orderOf s0 = 3 := orderOf_eq_prime s0_pow_three u0_pow_7_ne

theorem commute_y0_s0 : y0 * s0 = s0 * y0 := by
  rw [y0, s0, ← pow_add, ← pow_add, add_comm]

theorem trT_u0_pow_three : trT (u0 ^ 3) = GF8.ofNat' 4 := by
  unfold trT; rw [mat_u3]; decide +kernel

theorem trT_u0_pow_six : trT (u0 ^ 6) = GF8.ofNat' 6 := by
  unfold trT; rw [mat_u6]; decide +kernel

theorem trT_u0_pow_nine : trT (u0 ^ 9) = GF8.ofNat' 2 := by
  unfold trT; rw [mat_u9]; decide +kernel

theorem trT_u0_pow_twelve : trT (u0 ^ 12) = GF8.ofNat' 2 := by
  unfold trT; rw [mat_u12]; decide +kernel

theorem trT_u0_pow_fifteen : trT (u0 ^ 15) = GF8.ofNat' 6 := by
  unfold trT; rw [mat_u15]; decide +kernel

theorem trT_u0_pow_eighteen : trT (u0 ^ 18) = GF8.ofNat' 4 := by
  unfold trT; rw [mat_u18]; decide +kernel

theorem trT_y0_pow (n : ℕ) (hn : ¬ 7 ∣ n) :
    frobF (trT (y0 ^ n)) ≠ trT (y0 ^ n) ∧ frobF (frobF (trT (y0 ^ n))) ≠ trT (y0 ^ n) := by
  rw [pow_eq_pow_mod n y0_pow_seven]
  have hlt : n % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hne : n % 7 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  generalize n % 7 = k at hlt hne
  interval_cases k
  · exact absurd rfl hne
  · rw [y0, ← pow_mul, show 3 * 1 = 3 by norm_num, trT_u0_pow_three]; decide
  · rw [y0, ← pow_mul, show 3 * 2 = 6 by norm_num, trT_u0_pow_six]; decide
  · rw [y0, ← pow_mul, show 3 * 3 = 9 by norm_num, trT_u0_pow_nine]; decide
  · rw [y0, ← pow_mul, show 3 * 4 = 12 by norm_num, trT_u0_pow_twelve]; decide
  · rw [y0, ← pow_mul, show 3 * 5 = 15 by norm_num, trT_u0_pow_fifteen]; decide
  · rw [y0, ← pow_mul, show 3 * 6 = 18 by norm_num, trT_u0_pow_eighteen]; decide

end TD42

end CFSG.LocalAnalysis.GLTheoremA

end
