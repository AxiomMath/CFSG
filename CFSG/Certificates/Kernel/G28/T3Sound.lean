module

public import Certificates.Data.Kernel.G28.T3
public import CFSG.Certificates.Kernel.G28.Sound

public section

namespace CFSG.KC.G28

open CFSG.RankThree.PartTwo.Sec4.Item434G28
open CFSG.KC.Misc.G2U (pk fld_pk testBit_pk blt_land bld bld_eq pk_lt)

@[expose] def ph (p : ℕ × ℕ) : ℕ × ℕ := ((4 * p.1 + 5 * p.2) % 9, (3 * p.1 + 4 * p.2) % 9)

@[expose] def phI : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | c + 1, p => ph (phI c p)

theorem pcMul_eq (s t : ℕ) : pcMul s t = pcIdx (s / 27 + (phI (s % 3) (t / 27, t / 3 % 9)).1)
    (s / 3 % 9 + (phI (s % 3) (t / 27, t / 3 % 9)).2) (s % 3 + t % 3) := by
  simp only [pcMul, letN_eq]
  have hc : s % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize s % 3 = c at hc ⊢
  generalize t / 27 = a
  generalize t / 3 % 9 = b
  have h1 : cA 1 a b = 4 * a + 5 * b := rfl
  have h2 : cB 1 a b = 3 * a + 4 * b := rfl
  have h3 : cA 2 a b = 4 * a + 4 * b := rfl
  have h4 : cB 2 a b = 6 * a + 4 * b := rfl
  have p1 : phI 1 (a, b) = ph (a, b) := rfl
  have p2 : phI 2 (a, b) = ph (ph (a, b)) := rfl
  interval_cases c
  · rfl
  · rw [h1, h2, p1]
    simp only [ph, pcIdx]
    omega
  · rw [h3, h4, p2]
    simp only [ph, pcIdx]
    omega

section Monoid

variable {M : Type*} [Monoid M]

structure Rels (U Z O : M) : Prop where
  u9 : U ^ 9 = 1
  z9 : Z ^ 9 = 1
  o3 : O ^ 3 = 1
  uz : U * Z = Z * U
  ou : O * U = U ^ 4 * Z ^ 3 * O
  oz : O * Z = U ^ 5 * Z ^ 4 * O

@[expose] def fT (U Z O : M) (t : ℕ) : M := U ^ (t / 27) * Z ^ (t / 3 % 9) * O ^ (t % 3)

theorem pow_mod_of {x : M} {n : ℕ} (h : x ^ n = 1) (m : ℕ) : x ^ m = x ^ (m % n) := by
  conv_lhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, h, one_pow, one_mul]

variable {U Z O : M} (R : Rels U Z O)
include R

theorem E_mul (a b c d : ℕ) : U ^ a * Z ^ b * (U ^ c * Z ^ d) = U ^ (a + c) * Z ^ (b + d) := by
  have h : Z ^ b * U ^ c = U ^ c * Z ^ b := (Commute.pow_pow (R.uz : Commute U Z).symm b c).eq
  calc U ^ a * Z ^ b * (U ^ c * Z ^ d) = U ^ a * (Z ^ b * U ^ c) * Z ^ d := by
        simp only [mul_assoc]
    _ = U ^ a * (U ^ c * Z ^ b) * Z ^ d := by rw [h]
    _ = U ^ (a + c) * Z ^ (b + d) := by
        rw [pow_add, pow_add]
        simp only [mul_assoc]

theorem E_mod (a b : ℕ) : U ^ a * Z ^ b = U ^ (a % 9) * Z ^ (b % 9) := by
  rw [pow_mod_of R.u9 a, pow_mod_of R.z9 b]

theorem O_U (a : ℕ) : O * U ^ a = U ^ (4 * a) * Z ^ (3 * a) * O := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc O * U ^ (a + 1) = O * U ^ a * U := by rw [pow_succ, mul_assoc]
      _ = U ^ (4 * a) * Z ^ (3 * a) * (O * U) := by
          rw [ih]
          simp only [mul_assoc]
      _ = U ^ (4 * a) * Z ^ (3 * a) * (U ^ 4 * Z ^ 3) * O := by
          rw [R.ou]
          simp only [mul_assoc]
      _ = U ^ (4 * (a + 1)) * Z ^ (3 * (a + 1)) * O := by
          rw [E_mul R]
          ring_nf

theorem O_Z (b : ℕ) : O * Z ^ b = U ^ (5 * b) * Z ^ (4 * b) * O := by
  induction b with
  | zero => simp
  | succ b ih =>
    calc O * Z ^ (b + 1) = O * Z ^ b * Z := by rw [pow_succ, mul_assoc]
      _ = U ^ (5 * b) * Z ^ (4 * b) * (O * Z) := by
          rw [ih]
          simp only [mul_assoc]
      _ = U ^ (5 * b) * Z ^ (4 * b) * (U ^ 5 * Z ^ 4) * O := by
          rw [R.oz]
          simp only [mul_assoc]
      _ = U ^ (5 * (b + 1)) * Z ^ (4 * (b + 1)) * O := by
          rw [E_mul R]
          ring_nf

theorem O_E (p : ℕ × ℕ) : O * (U ^ p.1 * Z ^ p.2) = U ^ (ph p).1 * Z ^ (ph p).2 * O := by
  calc O * (U ^ p.1 * Z ^ p.2) = O * U ^ p.1 * Z ^ p.2 := by rw [mul_assoc]
    _ = U ^ (4 * p.1) * Z ^ (3 * p.1) * (O * Z ^ p.2) := by
        rw [O_U R]
        simp only [mul_assoc]
    _ = U ^ (4 * p.1) * Z ^ (3 * p.1) * (U ^ (5 * p.2) * Z ^ (4 * p.2)) * O := by
        rw [O_Z R]
        simp only [mul_assoc]
    _ = U ^ (ph p).1 * Z ^ (ph p).2 * O := by
        rw [E_mul R, E_mod R]
        simp only [ph]

theorem Opow_E (c : ℕ) (p : ℕ × ℕ) :
    O ^ c * (U ^ p.1 * Z ^ p.2) = U ^ (phI c p).1 * Z ^ (phI c p).2 * O ^ c := by
  induction c with
  | zero => simp [phI]
  | succ c ih =>
    calc O ^ (c + 1) * (U ^ p.1 * Z ^ p.2) = O * (O ^ c * (U ^ p.1 * Z ^ p.2)) := by
          rw [pow_succ', mul_assoc]
      _ = O * (U ^ (phI c p).1 * Z ^ (phI c p).2) * O ^ c := by
          rw [ih]
          simp only [mul_assoc]
      _ = U ^ (ph (phI c p)).1 * Z ^ (ph (phI c p)).2 * O * O ^ c := by rw [O_E R]
      _ = U ^ (phI (c + 1) p).1 * Z ^ (phI (c + 1) p).2 * O ^ (c + 1) := by
          rw [pow_succ' O c, ← mul_assoc]
          rfl

omit R in
theorem pcIdx_lt (a b c : ℕ) : pcIdx a b c < 243 := by
  unfold pcIdx
  omega

omit R in
theorem pcMul_lt (s t : ℕ) : pcMul s t < 243 := by
  rw [pcMul_eq]
  exact pcIdx_lt _ _ _

theorem fT_pcIdx (a b c : ℕ) : fT U Z O (pcIdx a b c) = U ^ a * Z ^ b * O ^ c := by
  have e1 : pcIdx a b c / 27 = a % 9 := by
    unfold pcIdx
    omega
  have e2 : pcIdx a b c / 3 % 9 = b % 9 := by
    unfold pcIdx
    omega
  have e3 : pcIdx a b c % 3 = c % 3 := by
    unfold pcIdx
    omega
  rw [fT, e1, e2, e3, ← E_mod R, ← pow_mod_of R.o3]

theorem fT_mul (s t : ℕ) : fT U Z O s * fT U Z O t = fT U Z O (pcMul s t) := by
  rw [pcMul_eq, fT_pcIdx R, fT, fT, pow_add O]
  have h := Opow_E R (s % 3) (t / 27, t / 3 % 9)
  calc U ^ (s / 27) * Z ^ (s / 3 % 9) * O ^ (s % 3) * (U ^ (t / 27) * Z ^ (t / 3 % 9) * O ^ (t % 3))
        = U ^ (s / 27) * Z ^ (s / 3 % 9) * (O ^ (s % 3) * (U ^ (t / 27) * Z ^ (t / 3 % 9))) *
          O ^ (t % 3) := by simp only [mul_assoc]
    _ = U ^ (s / 27) * Z ^ (s / 3 % 9) *
          (U ^ (phI (s % 3) (t / 27, t / 3 % 9)).1 * Z ^ (phI (s % 3) (t / 27, t / 3 % 9)).2) *
          (O ^ (s % 3) * O ^ (t % 3)) := by
        rw [h]
        simp only [mul_assoc]
    _ = _ := by rw [E_mul R]

omit R in
theorem fT_zero : fT U Z O 0 = 1 := by simp [fT]

theorem fT_pw (a x : ℕ) : fT U Z O (pw a x) = fT U Z O a ^ x := by
  induction x with
  | zero =>
    change fT U Z O 0 = _
    rw [pow_zero]
    exact fT_zero
  | succ x ih =>
    change fT U Z O (pcMul (pw a x) a) = _
    rw [← fT_mul R, ih, pow_succ]

end Monoid

theorem bldT_eq (w : ℕ) (f : ℕ → ℕ) (n : ℕ) : bldT w f n = bld w f n := rfl

theorem fld_eq (x o m : ℕ) : fld x o m = x / 2 ^ o % 2 ^ m := by
  change (x >>> o) &&& ((1 <<< m) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem bitT_eq (x p : ℕ) : bitT x p = x.testBit p := blt_land x p

theorem beq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  subst h
  exact Nat.beq_refl a

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem map_lt {f : ℕ → ℕ} {n B : ℕ} (hf : ∀ k < n, f k < B) :
    ∀ x ∈ (List.range n).map f, x < B := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  exact hf k (List.mem_range.1 hk)

theorem fld_bld {w : ℕ} {f : ℕ → ℕ} {n : ℕ} (hf : ∀ k < n, f k < 2 ^ w) {i : ℕ} (hi : i < n) :
    fld (bldT w f n) (w * i) w = f i := by
  rw [fld_eq, bldT_eq, bld_eq, fld_pk (map_lt hf) i,
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem fldT_bld {f : ℕ → ℕ} {n : ℕ} (hf : ∀ k < n, f k < 2 ^ 108) {i : ℕ} (hi : i < n) :
    fldT (bldT 108 f n) i = f i :=
  fld_bld hf hi

theorem bld_lt {w : ℕ} {f : ℕ → ℕ} {n : ℕ} (hf : ∀ k < n, f k < 2 ^ w) :
    bldT w f n < 2 ^ (w * n) := by
  rw [bldT_eq, bld_eq]
  have h := pk_lt (map_lt hf)
  rwa [List.length_map, List.length_range] at h

theorem testBit_bld {w : ℕ} {f : ℕ → ℕ} {n : ℕ} (hf : ∀ k < n, f k < 2 ^ w) {i k : ℕ}
    (hi : i < n) (hk : k < w) : (bldT w f n).testBit (w * i + k) = (f i).testBit k := by
  rw [bldT_eq, bld_eq, testBit_pk (map_lt hf) i hk,
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem boolNat_lt (b : Bool) : Bool.rec (motive := fun _ => ℕ) 0 1 b < 2 ^ 1 := by
  cases b <;> decide

theorem boolNat_bit (b : Bool) : (Bool.rec (motive := fun _ => ℕ) 0 1 b).testBit 0 = b := by
  cases b <;> rfl

theorem testBit_bld1 {f : ℕ → Bool} {n : ℕ} {i : ℕ} (hi : i < n) :
    (bldT 1 (fun e => Bool.rec (motive := fun _ => ℕ) 0 1 (f e)) n).testBit i = f i := by
  have h := testBit_bld (w := 1) (f := fun e => Bool.rec (motive := fun _ => ℕ) 0 1 (f e))
    (fun k _ => boolNat_lt _) hi (k := 0) (by norm_num)
  rw [Nat.one_mul, Nat.add_zero] at h
  rw [h, boolNat_bit]

theorem bld1_lt {f : ℕ → Bool} {n : ℕ} :
    bldT 1 (fun e => Bool.rec (motive := fun _ => ℕ) 0 1 (f e)) n < 2 ^ n := by
  have h := bld_lt (w := 1) (f := fun e => Bool.rec (motive := fun _ => ℕ) 0 1 (f e)) (n := n)
    (fun k _ => boolNat_lt _)
  rwa [Nat.one_mul] at h

theorem bldOr_bit {f : ℕ → ℕ} {e : ℕ} :
    ∀ n, (bldOr f n).testBit e = true → ∃ k < n, f k = e
  | 0, h => by simp [bldOr] at h
  | n + 1, h => by
    change (bldOr f n ||| (1 <<< f n)).testBit e = true at h
    rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | h
    · obtain ⟨k, hk, hk'⟩ := bldOr_bit n h
      exact ⟨k, by omega, hk'⟩
    · exact ⟨n, by omega, h⟩

theorem bldOr_lt {f : ℕ → ℕ} {B : ℕ} (hf : ∀ k, f k < B) : ∀ n, bldOr f n < 2 ^ B
  | 0 => Nat.two_pow_pos B
  | n + 1 => by
    change bldOr f n ||| (1 <<< f n) < 2 ^ B
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.or_lt_two_pow (bldOr_lt hf n) (Nat.pow_lt_pow_right (by norm_num) (hf n))

theorem mulP_lt (a b : ℕ) : mulP a b < 2 ^ 108 := by
  simp only [mulP, letN_eq]
  exact mulQ_lt _ _ _ _

theorem idP_lt : idP < 2 ^ 108 := by decide +kernel

theorem powP_lt (X k : ℕ) : powP X k < 2 ^ 108 := by
  cases k with
  | zero => exact idP_lt
  | succ k => exact mulP_lt _ _

theorem fldT_powT {X n i : ℕ} (hi : i < n) : fldT (powT X n) i = powP X i :=
  fldT_bld (fun k _ => powP_lt X k) hi

theorem maskI_lt (a b : ℕ) : maskI a b < 2 ^ 243 := bldOr_lt (fun _ => pcMul_lt _ _) 9

theorem maskI_bit {a b i : ℕ} (h : (maskI a b).testBit i = true) :
    ∃ x < 3, ∃ y < 3, pcMul (pw a x) (pw b y) = i := by
  obtain ⟨k, hk, e⟩ := bldOr_bit 9 h
  exact ⟨k / 3, by omega, k % 3, by omega, e⟩

theorem wT_bit {cg : List ℕ} {i v : ℕ} (hi : i < 243) (hv : v < 28)
    (h : (fldW (wT (maskT cg)) i).testBit v = true) :
    (maskI (cg.getD (2 * v) 0) (cg.getD (2 * v + 1) 0)).testBit i = true := by
  have e : fldW (wT (maskT cg)) i =
      bldT 1 (fun v => Bool.rec (motive := fun _ => ℕ) 0 1 (bitT (maskT cg) (243 * v + i))) 28 :=
    fld_bld (w := 28) (fun _ _ => bld1_lt) hi
  rw [e, testBit_bld1 hv, bitT_eq, maskT, testBit_bld (fun _ _ => maskI_lt _ _) hv hi] at h
  exact h

theorem wT_lt {cg : List ℕ} {i : ℕ} (hi : i < 243) : fldW (wT (maskT cg)) i < 2 ^ 28 := by
  have e : fldW (wT (maskT cg)) i =
      bldT 1 (fun v => Bool.rec (motive := fun _ => ℕ) 0 1 (bitT (maskT cg) (243 * v + i))) 28 :=
    fld_bld (w := 28) (fun _ _ => bld1_lt) hi
  rw [e]
  exact bld1_lt

theorem wT_common {cg : List ℕ} {i j : ℕ} (hi : i < 243) (hj : j < 243)
    (h : Nat.blt 0 (Nat.land (fldW (wT (maskT cg)) i) (fldW (wT (maskT cg)) j)) = true) :
    ∃ v < 28, (maskI (cg.getD (2 * v) 0) (cg.getD (2 * v + 1) 0)).testBit i = true ∧
      (maskI (cg.getD (2 * v) 0) (cg.getD (2 * v + 1) 0)).testBit j = true := by
  have hne : fldW (wT (maskT cg)) i &&& fldW (wT (maskT cg)) j ≠ 0 := by
    intro e
    change Nat.blt 0 (fldW (wT (maskT cg)) i &&& fldW (wT (maskT cg)) j) = true at h
    rw [e] at h
    exact absurd h (by decide)
  obtain ⟨v, hv⟩ := Nat.exists_testBit_of_ne_zero hne
  rw [Nat.testBit_and, Bool.and_eq_true] at hv
  have hv28 : v < 28 := by
    by_contra hc
    have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (wT_lt (cg := cg) hi)
      (Nat.pow_le_pow_right (by norm_num) (by omega : 28 ≤ v)))
    rw [hv.1] at this
    exact absurd this (by decide)
  exact ⟨v, hv28, wT_bit hi hv28 hv.1, wT_bit hj hv28 hv.2⟩

theorem decode_powCode {A : Array ℕ} (hA : Valid A) (k : ℕ) :
    decode (powCode A k) = decode A ^ k := by
  induction k with
  | zero => exact decode_idCode
  | succ k ih =>
    change decode (mulCode (powCode A k) A) = _
    rw [decode_mulCode (valid_powCode hA k) hA, ih, pow_succ]

theorem decode_eq_of_codeP {A B : Array ℕ} (hA : Valid A) (hB : Valid B)
    (h : codeP A = codeP B) : decode A = decode B := by
  rw [codeP_inj hA hB h]

theorem eq_of_beq_codeP {A B : Array ℕ} (hA : Valid A) (hB : Valid B) {x y : ℕ}
    (hx : codeP A = x) (hy : codeP B = y) (h : Nat.beq x y = true) : A = B :=
  codeP_inj hA hB (by rw [hx, hy]; exact Nat.eq_of_beq_eq_true h)

theorem getElem!_map_of {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (A : Array α)
    {v : ℕ} (hv : v < A.size) : (A.map f)[v]! = f A[v]! := by
  rw [getElem!_pos (A.map f) v (by simpa using hv), Array.getElem_map, getElem!_pos A v hv]

theorem conj_mul {g gi : Matrix (Fin 6) (Fin 6) CFSG.Quasithin.GF8} (h : g * gi = 1)
    (X Y : Matrix (Fin 6) (Fin 6) CFSG.Quasithin.GF8) :
    g * (X * Y) * gi = g * X * gi * (g * Y * gi) := by
  have h' : gi * g = 1 := mul_eq_one_comm.1 h
  calc g * (X * Y) * gi = g * X * (gi * g) * Y * gi := by rw [h']; simp only [mul_one, mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem conj_pow {g gi : Matrix (Fin 6) (Fin 6) CFSG.Quasithin.GF8} (h : g * gi = 1)
    (X : Matrix (Fin 6) (Fin 6) CFSG.Quasithin.GF8) (n : ℕ) :
    g * X ^ n * gi = (g * X * gi) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mul_one, h]
  | succ n ih => rw [pow_succ, pow_succ, conj_mul h, ih]

section Codes

variable {Uc Zc Oc : Array ℕ} (hU : Valid Uc) (hZ : Valid Zc) (hO : Valid Oc)
include hU hZ hO

theorem rels_of (h : relOK (codeP Uc) (codeP Zc) (codeP Oc) = true) :
    Rels (decode Uc) (decode Zc) (decode Oc) := by
  simp only [relOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hU4 := valid_powCode hU 4
  have hU5 := valid_powCode hU 5
  have hZ3 := valid_powCode hZ 3
  have hZ4 := valid_powCode hZ 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg decode (eq_of_beq_codeP (valid_powCode hU 9) valid_idCode
      (codeP_powCode hU 9) codeP_idCode h1)
    rwa [decode_powCode hU, decode_idCode] at this
  · have := congrArg decode (eq_of_beq_codeP (valid_powCode hZ 9) valid_idCode
      (codeP_powCode hZ 9) codeP_idCode h2)
    rwa [decode_powCode hZ, decode_idCode] at this
  · have := congrArg decode (eq_of_beq_codeP (valid_powCode hO 3) valid_idCode
      (codeP_powCode hO 3) codeP_idCode h3)
    rwa [decode_powCode hO, decode_idCode] at this
  · have := congrArg decode (eq_of_beq_codeP (valid_mulCode hU hZ) (valid_mulCode hZ hU)
      (codeP_mulCode hU hZ) (codeP_mulCode hZ hU) h4)
    rwa [decode_mulCode hU hZ, decode_mulCode hZ hU] at this
  · have := congrArg decode (eq_of_beq_codeP (valid_mulCode hO hU)
      (valid_mulCode (valid_mulCode hU4 hZ3) hO) (codeP_mulCode hO hU)
      (by rw [codeP_mulCode (valid_mulCode hU4 hZ3) hO, codeP_mulCode hU4 hZ3, codeP_powCode hU,
        codeP_powCode hZ]) h5)
    rwa [decode_mulCode hO hU, decode_mulCode (valid_mulCode hU4 hZ3) hO, decode_mulCode hU4 hZ3,
      decode_powCode hU, decode_powCode hZ] at this
  · have := congrArg decode (eq_of_beq_codeP (valid_mulCode hO hZ)
      (valid_mulCode (valid_mulCode hU5 hZ4) hO) (codeP_mulCode hO hZ)
      (by rw [codeP_mulCode (valid_mulCode hU5 hZ4) hO, codeP_mulCode hU5 hZ4, codeP_powCode hU,
        codeP_powCode hZ]) h6)
    rwa [decode_mulCode hO hZ, decode_mulCode (valid_mulCode hU5 hZ4) hO, decode_mulCode hU5 hZ4,
      decode_powCode hU, decode_powCode hZ] at this

theorem decode_t3 {t : ℕ} (ht : t < 243) :
    decode (t3List Uc Zc Oc)[t]! = fT (decode Uc) (decode Zc) (decode Oc) t := by
  rw [getElem!_t3List _ _ _ ht, decode_mulCode (valid_mulCode (valid_powCode hU _)
    (valid_powCode hZ _)) (valid_powCode hO _), decode_mulCode (valid_powCode hU _)
    (valid_powCode hZ _), decode_powCode hU, decode_powCode hZ, decode_powCode hO, fT]

theorem codeP_t3 {t : ℕ} (ht : t < 243) :
    codeP (t3List Uc Zc Oc)[t]! =
      elT (powT (codeP Uc) 9) (powT (codeP Zc) 9) (powT (codeP Oc) 3) t := by
  rw [getElem!_t3List _ _ _ ht, codeP_mulCode (valid_mulCode (valid_powCode hU _)
    (valid_powCode hZ _)) (valid_powCode hO _), codeP_mulCode (valid_powCode hU _)
    (valid_powCode hZ _), codeP_powCode hU, codeP_powCode hZ, codeP_powCode hO, elT,
    fldT_powT (by omega), fldT_powT (by omega), fldT_powT (by omega)]

theorem fldT_t3 {t : ℕ} (ht : t < 243) :
    fldT (bldT 108 (elT (powT (codeP Uc) 9) (powT (codeP Zc) 9) (powT (codeP Oc) 3)) 243) t =
      codeP (t3List Uc Zc Oc)[t]! := by
  rw [fldT_bld (f := elT (powT (codeP Uc) 9) (powT (codeP Zc) 9) (powT (codeP Oc) 3))
    (fun _ _ => mulP_lt _ _) ht, codeP_t3 hU hZ hO ht]

variable (R : Rels (decode Uc) (decode Zc) (decode Oc))
include R

theorem t3_mul {s t : ℕ} (hs : s < 243) (ht : t < 243) :
    mulCode (t3List Uc Zc Oc)[s]! (t3List Uc Zc Oc)[t]! = (t3List Uc Zc Oc)[pcMul s t]! :=
  eq_of_decode_eq (valid_mulCode (valid_t3List hU hZ hO hs) (valid_t3List hU hZ hO ht))
    (valid_t3List hU hZ hO (pcMul_lt s t)) (by
      rw [decode_mulCode (valid_t3List hU hZ hO hs) (valid_t3List hU hZ hO ht),
        decode_t3 hU hZ hO hs, decode_t3 hU hZ hO ht, decode_t3 hU hZ hO (pcMul_lt s t),
        fT_mul R])

omit R in
theorem t3_zero : (t3List Uc Zc Oc)[0]! = idCode :=
  eq_of_decode_eq (valid_t3List hU hZ hO (by norm_num)) valid_idCode (by
    rw [decode_t3 hU hZ hO (by norm_num), fT_zero, decode_idCode])

theorem t3_pow3 {s : ℕ} (hs : s < 243) :
    powCode (t3List Uc Zc Oc)[s]! 3 = (t3List Uc Zc Oc)[pc3 s]! :=
  eq_of_decode_eq (valid_powCode (valid_t3List hU hZ hO hs) 3)
    (valid_t3List hU hZ hO (pcMul_lt _ _)) (by
      rw [decode_powCode (valid_t3List hU hZ hO hs), decode_t3 hU hZ hO hs,
        decode_t3 hU hZ hO (t := pc3 s) (pcMul_lt _ _), pc3, ← fT_mul R, ← fT_mul R, pow_three,
        mul_assoc])

end Codes

theorem t3OK_of {L : Array (Array ℕ)} (h1 : L.size = 243) (h2 : L[0]! = idCode)
    (h3 : ∀ i < 243, ∀ j < i, L[i]! ≠ L[j]!)
    (h4 : ∀ i < 243, ∀ j < 243, ∃ k < 243, mulCode L[i]! L[j]! = L[k]!)
    (h5 : ∀ i < 243, ∃ j < 243, mulCode L[i]! L[j]! = idCode) : t3OK L = true := by
  simp only [t3OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq, List.any_eq_true, Array.contains_iff_mem]
  refine ⟨⟨⟨⟨h1, h2⟩, fun i hi j hj => h3 i hi j hj⟩, fun i hi j hj => ?_⟩, fun i hi => ?_⟩
  · obtain ⟨k, hk, e⟩ := h4 i hi j hj
    rw [e, getElem!_pos L k (by omega)]
    exact Array.getElem_mem _
  · obtain ⟨j, hj, e⟩ := h5 i hi
    exact ⟨j, hj, e⟩

theorem conjOK_of {L E0 gs gis : Array (Array ℕ)}
    (h1 : ∀ v < gs.size, mulCode gs[v]! gis[v]! = idCode)
    (h2 : ∀ i < 243, ∀ j < 243, goodPair L[i]! L[j]! = true → ∃ v < gs.size,
      (∃ m < E0.size, mulCode (mulCode gs[v]! L[i]!) gis[v]! = E0[m]!) ∧
      (∃ m < E0.size, mulCode (mulCode gs[v]! L[j]!) gis[v]! = E0[m]!)) :
    conjOK L E0 gs gis = true := by
  simp only [conjOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Array.contains_iff_mem]
  refine ⟨h1, fun i hi j hj => ?_⟩
  by_cases hg : goodPair L[i]! L[j]! = true
  · obtain ⟨v, hv, ⟨m, hm, e⟩, ⟨m', hm', e'⟩⟩ := h2 i hi j hj hg
    refine Or.inr ⟨v, hv, ?_, ?_⟩
    · rw [e, getElem!_pos E0 m hm]
      exact Array.getElem_mem _
    · rw [e', getElem!_pos E0 m' hm']
      exact Array.getElem_mem _
  · exact Or.inl (by simpa using hg)

theorem t3_of {Uc Zc Oc : Array ℕ} (hU : Valid Uc) (hZ : Valid Zc) (hO : Valid Oc)
    {cw : Array (List ℕ)} {cg : List ℕ}
    (h : t3ChkP (codeP Uc) (codeP Zc) (codeP Oc) cw.toList cg = true) :
    t3OK (t3List Uc Zc Oc) = true ∧ goodPair (powCode Uc 3) (powCode Zc 3) = true ∧
      conjOK (t3List Uc Zc Oc) (e0List (powCode Uc 3) (powCode Zc 3)) (cw.map wordCode)
        (cw.map invWordCode) = true := by
  simp only [t3ChkP, letB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨hrel, hinv⟩, hdist, hconj, hpair⟩ := h
  have R := rels_of hU hZ hO hrel
  set L := t3List Uc Zc Oc with hL
  have hV : ∀ {t}, t < 243 → Valid L[t]! := fun ht => valid_t3List hU hZ hO ht
  have hd : ∀ i < 243, ∀ j < i, L[i]! ≠ L[j]! := by
    simp only [distinctT, List.all_eq_true, List.mem_range, letB_eq, Bool.not_eq_true'] at hdist
    intro i hi j hj e
    have := hdist i hi j hj
    rw [fldT_t3 hU hZ hO hi, fldT_t3 hU hZ hO (by omega), e, Nat.beq_refl] at this
    exact absurd this (by decide)
  have hinj : ∀ i < 243, ∀ j < 243, L[i]! = L[j]! → i = j := by
    intro i hi j hj e
    rcases lt_trichotomy i j with h | h | h
    · exact absurd e.symm (hd j hj i h)
    · exact h
    · exact absurd e (hd i hi j h)
  have h0 : L[0]! = idCode := t3_zero hU hZ hO
  have hmul : ∀ {s t}, s < 243 → t < 243 → mulCode L[s]! L[t]! = L[pcMul s t]! :=
    fun hs ht => t3_mul hU hZ hO R hs ht
  have hpow : ∀ {s}, s < 243 → powCode L[s]! 3 = L[pc3 s]! := fun hs => t3_pow3 hU hZ hO R hs
  have hpc3 : ∀ s, pc3 s < 243 := fun s => pcMul_lt _ _
  have hgood : ∀ i < 243, ∀ j < 243, goodPair L[i]! L[j]! = true ↔
      (i ≠ 0 ∧ pc3 i = 0 ∧ pc3 j = 0 ∧ pcMul i j = pcMul j i ∧ j ≠ 0 ∧ j ≠ i ∧
        j ≠ pcMul i i) := by
    intro i hi j hj
    have e0 : ∀ {k}, k < 243 → (L[k]! = idCode ↔ k = 0) := fun hk => by
      rw [← h0]
      exact ⟨hinj _ hk 0 (by norm_num), fun e => by rw [e]⟩
    constructor
    · intro hg
      obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := goodPair_spec hg
      rw [hpow hi, e0 (hpc3 _)] at g2
      rw [hpow hj, e0 (hpc3 _)] at g3
      rw [hmul hi hj, hmul hj hi] at g4
      rw [hmul hi hi] at g7
      exact ⟨fun e => g1 ((e0 hi).2 e), g2, g3, hinj _ (pcMul_lt _ _) _ (pcMul_lt _ _) g4,
        fun e => g5 ((e0 hj).2 e), fun e => g6 (by rw [e]),
        fun e => g7 (by rw [e])⟩
    · rintro ⟨g1, g2, g3, g4, g5, g6, g7⟩
      refine goodPair_of (fun e => g1 ((e0 hi).1 e)) (by rw [hpow hi, g2, h0])
        (by rw [hpow hj, g3, h0]) (by rw [hmul hi hj, hmul hj hi, g4])
        (fun e => g5 ((e0 hj).1 e)) (fun e => g6 (hinj _ hj _ hi e))
        (fun e => g7 (hinj _ hj _ (pcMul_lt _ _) (by rw [e, hmul hi hi])))
  have hu : powCode Uc 3 = L[81]! := eq_of_decode_eq (valid_powCode hU 3) (hV (by norm_num)) (by
    rw [decode_powCode hU, decode_t3 hU hZ hO (by norm_num), fT]
    norm_num)
  have hz : powCode Zc 3 = L[9]! := eq_of_decode_eq (valid_powCode hZ 3) (hV (by norm_num)) (by
    rw [decode_powCode hZ, decode_t3 hU hZ hO (by norm_num), fT]
    norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp only [pcInvOK, List.all_eq_true, List.mem_range] at hinv
    refine t3OK_of (size_t3List _ _ _) h0 hd (fun i hi j hj => ⟨_, pcMul_lt i j, hmul hi hj⟩)
      (fun i hi => ⟨pcInv i, pcMul_lt _ _, ?_⟩)
    rw [hmul (t := pcInv i) hi (pcMul_lt _ _), Nat.eq_of_beq_eq_true (hinv i hi), h0]
  · rw [hu, hz, hgood 81 (by norm_num) 9 (by norm_num)]
    refine ⟨by norm_num, ?_, ?_, ?_, by norm_num, by norm_num, ?_⟩ <;> decide +kernel
  · simp only [conjChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, letB_eq,
      Nat.blt_eq] at hconj
    obtain ⟨hlen, hv⟩ := hconj
    have hlen' : cw.size = 28 := by
      have := Nat.eq_of_beq_eq_true hlen
      rwa [Array.length_toList] at this
    have hw : ∀ v < 28, mulCode (wordCode cw[v]!) (wordCode cw[v]!.reverse) = idCode ∧
        cg.getD (2 * v) 0 < 243 ∧ cg.getD (2 * v + 1) 0 < 243 ∧
        mulCode (mulCode (wordCode cw[v]!) L[cg.getD (2 * v) 0]!) (wordCode cw[v]!.reverse) =
          powCode Uc 3 ∧
        mulCode (mulCode (wordCode cw[v]!) L[cg.getD (2 * v + 1) 0]!)
          (wordCode cw[v]!.reverse) = powCode Zc 3 := by
      intro v hv28
      obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩ := hv v hv28
      rw [← getElem!_list] at e1 e4 e5
      have vg := valid_wordCode cw[v]!
      have vgi := valid_wordCode cw[v]!.reverse
      refine ⟨eq_of_beq_codeP (valid_mulCode vg vgi) valid_idCode
        (by rw [codeP_mulCode vg vgi, codeP_wordCode, codeP_wordCode]) codeP_idCode e1, e2, e3,
        ?_, ?_⟩
      · refine eq_of_beq_codeP (valid_mulCode (valid_mulCode vg (hV e2)) vgi)
          (valid_powCode hU 3) ?_ (codeP_powCode hU 3) e4
        rw [codeP_mulCode (valid_mulCode vg (hV e2)) vgi, codeP_mulCode vg (hV e2),
          codeP_wordCode, codeP_wordCode, ← fldT_t3 hU hZ hO e2]
      · refine eq_of_beq_codeP (valid_mulCode (valid_mulCode vg (hV e3)) vgi)
          (valid_powCode hZ 3) ?_ (codeP_powCode hZ 3) e5
        rw [codeP_mulCode (valid_mulCode vg (hV e3)) vgi, codeP_mulCode vg (hV e3),
          codeP_wordCode, codeP_wordCode, ← fldT_t3 hU hZ hO e3]
    have hset : ∀ v < 28, ∀ i, (maskI (cg.getD (2 * v) 0) (cg.getD (2 * v + 1) 0)).testBit i =
        true → i < 243 → ∃ m < 9, mulCode (mulCode (wordCode cw[v]!) L[i]!)
          (wordCode cw[v]!.reverse) = (e0List (powCode Uc 3) (powCode Zc 3))[m]! := by
      intro v hv28 i hb hi
      obtain ⟨w1, w2, w3, w4, w5⟩ := hw v hv28
      obtain ⟨x, hx, y, hy, rfl⟩ := maskI_bit hb
      have vg := valid_wordCode cw[v]!
      have vgi := valid_wordCode cw[v]!.reverse
      have dg : decode (wordCode cw[v]!) * decode (wordCode cw[v]!.reverse) = 1 := by
        rw [← decode_mulCode vg vgi, w1, decode_idCode]
      have da := congrArg decode w4
      have db := congrArg decode w5
      rw [decode_mulCode (valid_mulCode vg (hV w2)) vgi, decode_mulCode vg (hV w2),
        decode_t3 hU hZ hO w2] at da
      rw [decode_mulCode (valid_mulCode vg (hV w3)) vgi, decode_mulCode vg (hV w3),
        decode_t3 hU hZ hO w3] at db
      have ex : (3 * x + y) / 3 = x := by omega
      have ey : (3 * x + y) % 3 = y := by omega
      refine ⟨3 * x + y, by omega, eq_of_decode_eq
        (valid_mulCode (valid_mulCode vg (hV hi)) vgi)
        (valid_e0List (valid_powCode hU 3) (valid_powCode hZ 3) (by omega)) ?_⟩
      rw [decode_mulCode (valid_mulCode vg (hV hi)) vgi, decode_mulCode vg (hV hi),
        decode_t3 hU hZ hO hi, ← fT_mul R, fT_pw R, fT_pw R, conj_mul dg, conj_pow dg,
        conj_pow dg, da, db, getElem!_e0List _ _ (by omega), ex, ey,
        decode_mulCode (valid_powCode (valid_powCode hU 3) _) (valid_powCode (valid_powCode hZ 3) _),
        decode_powCode (valid_powCode hU 3), decode_powCode (valid_powCode hZ 3)]
    have hsz : ∀ v < 28, (cw.map wordCode)[v]! = wordCode cw[v]! ∧
        (cw.map invWordCode)[v]! = wordCode cw[v]!.reverse := fun v hv28 =>
      ⟨getElem!_map_of _ cw (by omega), getElem!_map_of _ cw (by omega)⟩
    refine conjOK_of (fun v hv28 => ?_) (fun i hi j hj hg => ?_)
    · rw [Array.size_map] at hv28
      rw [(hsz v (by omega)).1, (hsz v (by omega)).2]
      exact (hw v (by omega)).1
    · obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := (hgood i hi j hj).1 hg
      simp only [pairOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
        letB_eq] at hpair
      have hO3 : ∀ k < 243, bitT o3T k = Nat.beq (pc3 k) 0 := fun k hk => by
        rw [bitT_eq, o3T, testBit_bld1 hk]
      rcases hpair i hi with (e | e) | e
      · exact absurd (Nat.eq_of_beq_eq_true e) g1
      · rw [hO3 i hi, beq_true g2] at e
        exact absurd e (by decide)
      · rcases e j hj with e | e
        · have : goodI o3T i (pcMul i i) j = true := by
            simp only [goodI, Bool.and_eq_true, Bool.not_eq_true', hO3 j hj]
            exact ⟨⟨⟨⟨beq_false g5, beq_false g6⟩, beq_true g3⟩, beq_false g7⟩, beq_true g4⟩
          rw [this] at e
          exact absurd e (by decide)
        · obtain ⟨v, hv28, bi, bj⟩ := wT_common hi hj e
          refine ⟨v, by rw [Array.size_map]; omega, ?_, ?_⟩
          · obtain ⟨m, hm, em⟩ := hset v hv28 i bi hi
            refine ⟨m, by rw [size_e0List]; exact hm, ?_⟩
            rw [(hsz v hv28).1, (hsz v hv28).2]
            exact em
          · obtain ⟨m, hm, em⟩ := hset v hv28 j bj hj
            refine ⟨m, by rw [size_e0List]; exact hm, ?_⟩
            rw [(hsz v hv28).1, (hsz v hv28).2]
            exact em

end CFSG.KC.G28

end
