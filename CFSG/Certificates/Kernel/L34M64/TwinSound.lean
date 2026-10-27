module

public import Certificates.Data.Kernel.L34M64.Twin
public import CFSG.Certificates.Kernel.HMathieu.FixTabSound

public section

namespace CFSG.KC.L34M64

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H13.Ch9.L34M
  CFSG.Quasithin.H.Mathieu

@[expose] def RepP (P : ℕ) (A : Matrix (Fin 8) (Fin 8) F4) : Prop :=
  ∀ i j : Fin 8, ln P (8 * i.val + j.val) = (A i j).code.val

theorem land_three (x : ℕ) : Nat.land x 3 = x % 4 := Nat.and_two_pow_sub_one_eq_mod x 2

theorem ln_eq (P k : ℕ) : ln P k = P / 4 ^ k % 4 := by
  have h4 : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have h1 : Nat.shiftRight P (Nat.mul 2 k) = P / 4 ^ k := by
    rw [h4]
    exact Nat.shiftRight_eq_div_pow P (2 * k)
  rw [ln, h1, land_three]

theorem ln_lt (P k : ℕ) : ln P k < 4 := by
  rw [ln_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem pk_succ (f : ℕ → ℕ) (n : ℕ) : pk f (n + 1) = pk f n + f n * 4 ^ n := by
  have h : pk f (n + 1) = pk f n + f n <<< (2 * n) := rfl
  rw [h, Nat.shiftLeft_eq, pow_mul]
  norm_num

theorem pk_lt {f : ℕ → ℕ} (hf : ∀ p, f p < 4) : ∀ n, pk f n < 4 ^ n
  | 0 => by
    have h : pk f 0 = 0 := rfl
    rw [h]
    norm_num
  | n + 1 => by
    have ih := pk_lt hf n
    have h := hf n
    rw [pk_succ, pow_succ]
    have : f n * 4 ^ n ≤ 3 * 4 ^ n := Nat.mul_le_mul_right _ (by omega)
    omega

theorem ln_pk {f : ℕ → ℕ} (hf : ∀ p, f p < 4) : ∀ {n k : ℕ}, k < n → ln (pk f n) k = f k
  | 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, hk => by
    rw [ln_eq, pk_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · have ih := ln_pk hf hk
      rw [ln_eq] at ih
      obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
      have e : f (k + 1 + d) * 4 ^ (k + 1 + d) = (4 * (f (k + 1 + d) * 4 ^ d)) * 4 ^ k := by
        rw [pow_add, pow_add, pow_one]
        ring
      rw [e, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_left]
      exact ih
    · have hlt := pk_lt hf k
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
      exact Nat.mod_eq_of_lt (hf k)

theorem ln_pk64 {f : ℕ → ℕ} (hf : ∀ p, f p < 4) (i j : Fin 8) :
    ln (pk f 64) (8 * i.val + j.val) = f (8 * i.val + j.val) :=
  ln_pk hf (by omega)

theorem div8 (i j : Fin 8) : Nat.div (8 * i.val + j.val) 8 = i.val := by
  change (8 * i.val + j.val) / 8 = i.val
  omega

theorem mod8 (i j : Fin 8) : Nat.mod (8 * i.val + j.val) 8 = j.val := by
  change (8 * i.val + j.val) % 8 = j.val
  omega

theorem mulT_lt (a b : ℕ) : mulT a b < 4 := by
  unfold mulT
  rw [land_three]
  exact Nat.mod_lt _ (by norm_num)

theorem mulT_eq {a b : ℕ} (ha : a < 4) (hb : b < 4) : mulT a b = mulN a b := by
  interval_cases a <;> interval_cases b <;> rfl

theorem xr_eight (f : ℕ → ℕ) : xr f 8 = xor8 f := by
  have h : xr f 8 = 0 ^^^ f 0 ^^^ f 1 ^^^ f 2 ^^^ f 3 ^^^ f 4 ^^^ f 5 ^^^ f 6 ^^^ f 7 := rfl
  rw [h, Nat.zero_xor]
  rfl

theorem xr_lt {f : ℕ → ℕ} (hf : ∀ l, f l < 4) : ∀ n, xr f n < 4
  | 0 => by
    have h : xr f 0 = 0 := rfl
    rw [h]
    norm_num
  | n + 1 => by
    have h : xr f (n + 1) = xr f n ^^^ f n := rfl
    rw [h]
    exact Nat.xor_lt_two_pow (n := 2) (xr_lt hf n) (hf n)

theorem rep_mulP {P Q : ℕ} {A B : Matrix (Fin 8) (Fin 8) F4} (hA : RepP P A) (hB : RepP Q B) :
    RepP (mulP P Q) (A * B) := by
  intro i j
  rw [mulP, ln_pk64 (fun p => xr_lt (fun l => mulT_lt _ _) 8), div8, mod8, xr_eight,
    Matrix.mul_apply, code_sum8]
  refine xor8_congr fun l hl => ?_
  rw [dite_eq_left hl, code_mul, ← hA i ⟨l, hl⟩, ← hB ⟨l, hl⟩ j]
  exact mulT_eq (ln_lt _ _) (ln_lt _ _)

theorem bt_eq (m k : ℕ) : bt m k = bitN m k := by
  have h1 : Nat.land (Nat.shiftRight m k) 1 = m / 2 ^ k % 2 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact Nat.and_one_is_mod _
  rw [bt, h1, bitN, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with h | h <;> simp [h]

theorem bt_lt (m k : ℕ) : bt m k < 2 := by
  rw [bt_eq, bitN]
  split_ifs <;> norm_num

theorem upc_lt (m i j : ℕ) : upc m i j < 4 := by
  have h1 := bt_lt m (Nat.add (Nat.mul 8 i) j)
  have h2 := bt_lt m (Nat.add (Nat.mul 8 j) i)
  change bt m (Nat.add (Nat.mul 8 i) j) + 2 * bt m (Nat.add (Nat.mul 8 j) i) < 4
  omega

theorem ycK_eq {m i j : ℕ} : ycK m i j = ycode m i j := by
  have hu : ∀ a b, upc m a b = bitN m (8 * a + b) + 2 * bitN m (8 * b + a) := fun a b => by
    rw [upc, bt_eq, bt_eq]
    rfl
  unfold ycK ycode
  cases hij : Nat.blt i j
  · have hij' : ¬ i < j := by
      intro h
      rw [← Nat.blt_eq] at h
      rw [h] at hij
      exact absurd hij (by decide)
    cases hji : Nat.blt j i
    · have hji' : ¬ j < i := by
        intro h
        rw [← Nat.blt_eq] at h
        rw [h] at hji
        exact absurd hji (by decide)
      simp only [hij', hji', if_false]
      rw [bt_eq]
      rfl
    · have hji' : j < i := by
        rw [← Nat.blt_eq]
        exact hji
      simp only [hij', hji', if_false, if_true]
      rw [mulT_eq (upc_lt _ _ _) (upc_lt _ _ _), hu]
  · have hij' : i < j := by
      rw [← Nat.blt_eq]
      exact hij
    simp only [hij', if_true]
    rw [hu]

theorem ycK_lt (m i j : ℕ) : ycK m i j < 4 := by
  unfold ycK
  cases Nat.blt i j
  · cases Nat.blt j i
    · have := bt_lt m (Nat.add (Nat.mul 8 i) i)
      change bt m _ < 4
      omega
    · exact mulT_lt _ _
  · exact upc_lt _ _ _

theorem rep_yP (m : ℕ) : RepP (yP m) (herm8 m) := by
  intro i j
  rw [yP, ln_pk64 (fun p => ycK_lt _ _ _), div8, mod8, ycK_eq, herm8_code]

theorem rep_starP {P : ℕ} {R : Matrix (Fin 8) (Fin 8) F4} (hR : RepP P R) :
    RepP (starP P) (barM R)ᵀ := by
  intro i j
  rw [starP, ln_pk64 (fun p => mulT_lt _ _), div8, mod8, transpose_apply, barM_apply, code_cj,
    ← hR j i]
  exact mulT_eq (ln_lt _ _) (ln_lt _ _)

theorem rep_cjP {P : ℕ} {A : Matrix (Fin 8) (Fin 8) F4} (hA : RepP P A) :
    RepP (cjP P) (barM A) := by
  intro i j
  rw [cjP, ln_pk64 (fun p => mulT_lt _ _), barM_apply, code_cj, ← hA i j]
  exact mulT_eq (ln_lt _ _) (ln_lt _ _)

theorem maskOf_eq_sum : ∀ (n : ℕ) (v : Fin n → ZMod 2),
    maskOf n v = ∑ i : Fin n, (v i).val * 2 ^ i.val
  | 0, v => by simp [maskOf]
  | n + 1, v => by
    rw [maskOf, maskOf_eq_sum n, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem maskLoop_eq (Z : ℕ) : ∀ n : ℕ,
    (Nat.rec 0 (fun p acc => Nat.add acc (Nat.shiftLeft (mbit Z (Nat.div p 8) (Nat.mod p 8)) p))
      n : ℕ) = ∑ p ∈ Finset.range n, mbit Z (p / 8) (p % 8) * 2 ^ p
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← maskLoop_eq Z n, ← Nat.shiftLeft_eq]
    rfl

theorem mbit_eq {Z : ℕ} {A : Matrix (Fin 8) (Fin 8) F4} (hZ : RepP Z A) (p : Fin 64) :
    mbit Z (p.val / 8) (p.val % 8) = (code8V A p).val := by
  have hr : (row8 p).val = p.val / 8 := rfl
  have hc : (col8 p).val = p.val % 8 := rfl
  have hl : ∀ x : ℕ, Nat.land x 1 = x % 2 := Nat.and_one_is_mod
  have hcd : ∀ x : F4, x.code.val < 4 := fun x => x.code.isLt
  unfold mbit code8V lo hi
  cases hrc : Nat.blt (p.val / 8) (p.val % 8)
  · have hrc' : ¬ row8 p < col8 p := by
      rw [Fin.lt_def, hr, hc, ← Nat.blt_eq, hrc]
      exact Bool.false_ne_true
    cases hcr : Nat.blt (p.val % 8) (p.val / 8)
    · have hcr' : ¬ col8 p < row8 p := by
        rw [Fin.lt_def, hr, hc, ← Nat.blt_eq, hcr]
        exact Bool.false_ne_true
      simp only [hrc', hcr', if_false]
      rw [ZMod.val_natCast]
      have e := hZ (row8 p) (row8 p)
      rw [hr] at e
      change Nat.land (ln Z (8 * (p.val / 8) + p.val / 8)) 1 = _
      rw [e, hl, Nat.mod_mod]
    · have hcr' : col8 p < row8 p := by
        rw [Fin.lt_def, hr, hc, ← Nat.blt_eq]
        exact hcr
      simp only [hrc', hcr', if_false, if_true]
      rw [ZMod.val_natCast]
      have e := hZ (col8 p) (row8 p)
      rw [hr, hc] at e
      change Nat.shiftRight (ln Z (8 * (p.val % 8) + p.val / 8)) 1 = _
      have hs : ∀ x, Nat.shiftRight x 1 = x / 2 := fun x => by
        simpa using Nat.shiftRight_eq_div_pow x 1
      rw [e, hs]
      have := hcd (A (col8 p) (row8 p))
      omega
  · have hrc' : row8 p < col8 p := by
      rw [Fin.lt_def, hr, hc, ← Nat.blt_eq]
      exact hrc
    simp only [hrc', if_true]
    rw [ZMod.val_natCast]
    have e := hZ (row8 p) (col8 p)
    rw [hr, hc] at e
    change Nat.land (ln Z (8 * (p.val / 8) + p.val % 8)) 1 = _
    rw [e, hl, Nat.mod_mod]

theorem maskP_eq {Z : ℕ} {A : Matrix (Fin 8) (Fin 8) F4} (hZ : RepP Z A) : maskP Z = code8 A := by
  have h1 : maskP Z = ∑ p ∈ Finset.range 64, mbit Z (p / 8) (p % 8) * 2 ^ p := maskLoop_eq Z 64
  rw [h1, Finset.sum_range, code8, maskOf_eq_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mbit_eq hZ p]

theorem actP_eq {P : ℕ} {R : Matrix (Fin 8) (Fin 8) F4} (hR : RepP P R) (m : ℕ) :
    actP P m = actH8 R m := by
  rw [actP, maskP_eq (rep_mulP (rep_mulP hR (rep_yP m)) (rep_starP hR)), actH8]

theorem fldP_eq (m : ℕ) : fldP m = fld64N m := by
  rw [fldP, maskP_eq (rep_cjP (rep_yP m)), fld64N]

theorem colsChk_aux (F : ℕ → ℕ) : ∀ (L : List ℕ) (s : ℕ), colsChk F L s = true →
    s + L.length = 64 ∧ L = (List.range' s L.length).map fun j => F (2 ^ j)
  | [], s, h => by
    have h' : Nat.beq s 64 = true := h
    rw [Nat.beq_eq] at h'
    simp [h']
  | c :: L, s, h => by
    have h' : Bool.rec false (colsChk F L (s + 1)) (Nat.beq (F (Nat.shiftLeft 1 s)) c) = true := h
    cases hb : Nat.beq (F (Nat.shiftLeft 1 s)) c
    · rw [hb] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hb] at h'
      have ih := colsChk_aux F L (s + 1) h'
      rw [Nat.beq_eq] at hb
      have hb' : F (2 ^ s) = c := by
        rw [← Nat.one_shiftLeft]
        exact hb
      refine ⟨by simp only [List.length_cons]; omega, ?_⟩
      rw [List.length_cons, List.range'_succ, List.map_cons, hb', ← ih.2]

theorem colsChk_spec {F : ℕ → ℕ} {L : List ℕ} (h : colsChk F L 0 = true) : L = matOf 64 F := by
  have h' := colsChk_aux F L 0 h
  rw [zero_add] at h'
  rw [matOf, List.range_eq_range', ← h'.1]
  exact h'.2

theorem allB_spec {g : ℕ → Bool} : ∀ {n : ℕ}, allB g n = true → ∀ k < n, g k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    have h' : Bool.rec false (g n) (allB g n) = true := h
    cases hb : allB g n
    · rw [hb] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hb] at h'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact allB_spec hb k hk
      · exact h'

theorem codesChk_spec {P : ℕ} {A : Matrix (Fin 8) (Fin 8) F4} (h : codesChk P A = true) :
    RepP P A := by
  intro i j
  have hk : 8 * i.val + j.val < 64 := by omega
  have e := allB_spec h _ hk
  simp only [Nat.beq_eq] at e
  rw [e, entC, dif_pos hk]
  rw [show (⟨8 * i.val + j.val, hk⟩ : Fin 64) = pos8 i j from rfl, row8_pos8, col8_pos8]

open CFSG.KC.HMathieu

theorem compK_eq (cs ds : List ℕ) : compK cs ds = CFSG.Quasithin.H13.Ch9.L34M.comp cs ds := by
  rw [compK, CFSG.Quasithin.H13.Ch9.L34M.comp, actK_fun]

theorem isInvK_eq : isInvK = isInvC64 := by
  funext cs
  simp only [isInvK, isInvC64, actK_fun]

theorem pickWitK_eq (n r : ℕ) (cs : List ℕ) : pickWitK n r cs = pickWit n r cs := by
  simp only [pickWitK, pickWit, actK_fun]

theorem chk1K_eq (n : ℕ) (dat : List (List ℕ × List ℕ)) : chk1K n dat = chk1 n dat := by
  simp only [chk1K, chk1, rankOKK, rankOK, nonQuadK, nonQuad, actK_fun]

end CFSG.KC.L34M64
