module

public import CFSG.F3.ConjSpec
public import CFSG.F3.SepSpec
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import CFSG.Certificates.Kernel.Spor.PK.MiscBase
public import CFSG.LieType.Multipliers.F42Data
public import Certificates.Data.Kernel.Misc.F42

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.F42 CFSG.F3.Native
open CFSG.LieType.Multipliers.F42 (eqPM commutes)

theorem nthV_eq (l : List ℕ) (i : ℕ) : nthV l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      show nthV xs j = (x :: xs).getD (j + 1) 0
      rw [List.getD_cons_succ, ih j]

abbrev Can52 (X : Array V) : Prop := canonM 52 X = true

private theorem testBit_lt_52 {x : ℕ} (hx : x < 2 ^ 52) {k : ℕ} (hk : 52 ≤ k) :
    x.testBit k = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk))

private theorem val_eq_zero_of_lt {a : V} (hp : a.p < 2 ^ 52) (hm : a.m < 2 ^ 52) {k : ℕ}
    (hk : 52 ≤ k) : a.val k = 0 := by
  rw [V.val_eq_bitVal, testBit_lt_52 hp hk, testBit_lt_52 hm hk]
  rfl

private theorem lt_of_val_zero {a : V} (h : ∀ k, 52 ≤ k → a.val k = 0) :
    a.p < 2 ^ 52 ∧ a.m < 2 ^ 52 := by
  have h1 : (1 : ZMod 3) ≠ 0 := by decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have key : ∀ k, 52 ≤ k → a.p.testBit k = false ∧ a.m.testBit k = false := by
    intro k hk
    have := h k hk
    rw [V.val_eq_bitVal] at this
    revert this
    cases a.p.testBit k <;> cases a.m.testBit k <;> simp [bitVal, h1, h2]
  exact ⟨Nat.lt_pow_two_of_testBit _ fun k hk => (key k hk).1,
    Nat.lt_pow_two_of_testBit _ fun k hk => (key k hk).2⟩

private theorem canon52_of_val {a : V} (hw : a.wf = true) (h : ∀ k, 52 ≤ k → a.val k = 0) :
    a.p < 2 ^ 52 ∧ a.m < 2 ^ 52 ∧ a.p &&& a.m = 0 := by
  refine ⟨(lt_of_val_zero h).1, (lt_of_val_zero h).2, ?_⟩
  unfold V.wf at hw
  exact beq_iff_eq.1 hw

private theorem canonV_iff {a : V} :
    (a.wf && a.p >>> 52 == 0 && a.m >>> 52 == 0) = true ↔
      a.p < 2 ^ 52 ∧ a.m < 2 ^ 52 ∧ a.p &&& a.m = 0 := by
  simp only [V.wf, Bool.and_eq_true, beq_iff_eq, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_zero_iff_lt (Nat.two_pow_pos 52)]
  tauto

theorem can52_iff {X : Array V} : Can52 X ↔ X.size = 52 ∧
    ∀ i < 52, X[i]!.p < 2 ^ 52 ∧ X[i]!.m < 2 ^ 52 ∧ X[i]!.p &&& X[i]!.m = 0 := by
  constructor
  · intro h
    obtain ⟨hs, hv⟩ := canonM_spec h
    exact ⟨hs, fun i hi => canonV_iff.1 (hv i (by omega))⟩
  · rintro ⟨hs, hv⟩
    unfold Can52 canonM
    rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
    refine ⟨hs, fun i hi => ?_⟩
    have hi' : i < 52 := by omega
    rw [← getElem!_pos X i hi]
    exact canonV_iff.2 (hv i hi')

theorem can52_idM : Can52 (idM 52) := canonM_idM 52

theorem can52_mul {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) : Can52 (mul 52 X Y) := by
  obtain ⟨hXs, -⟩ := can52_iff.1 hX
  have hXw := RowsWF.of_canonM hX
  have hYw := RowsWF.of_canonM hY
  have hYc := (can52_iff.1 hY).2
  refine can52_iff.2 ⟨by rw [mul_size, hXs], fun i hi => ?_⟩
  rw [mul_getElem! (by omega)]
  refine canon52_of_val (V.wf_comb 52 Y _ hYw (hXw i)) fun k hk => ?_
  rw [V.val_comb 52 Y _ hYw (hXw i)]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : j < 52 := Finset.mem_range.1 hj
  rw [val_eq_zero_of_lt (hYc j hj').1 (hYc j hj').2.1 hk, mul_zero]

theorem can52_negM {X : Array V} (hX : Can52 X) : Can52 (CFSG.F3.Native.negM X) := by
  obtain ⟨hXs, hXc⟩ := can52_iff.1 hX
  refine can52_iff.2 ⟨by rw [negM_size, hXs], fun i hi => ?_⟩
  have hi' : i < X.size := by omega
  have e : (CFSG.F3.Native.negM X)[i]! = (X[i]!).neg := by
    unfold CFSG.F3.Native.negM
    rw [getElem!_pos _ i (by simpa using hi'), Array.getElem_map, getElem!_pos X i hi']
  rw [e]
  obtain ⟨h1, h2, h3⟩ := hXc i hi
  exact ⟨h2, h1, by simpa [V.neg, Nat.and_comm] using h3⟩

theorem can52_addM {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) : Can52 (addM 52 X Y) := by
  have hXw := RowsWF.of_canonM hX
  have hYw := RowsWF.of_canonM hY
  have hXc := (can52_iff.1 hX).2
  have hYc := (can52_iff.1 hY).2
  refine can52_iff.2 ⟨addM_size 52 X Y, fun i hi => ?_⟩
  have e : (addM 52 X Y)[i]! = (X[i]!).add (Y[i]!) := by
    unfold CFSG.F3.Native.addM
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  rw [e]
  refine canon52_of_val (V.wf_add (hXw i) (hYw i)) fun k hk => ?_
  rw [V.val_add (hXw i) (hYw i), val_eq_zero_of_lt (hXc i hi).1 (hXc i hi).2.1 hk,
    val_eq_zero_of_lt (hYc i hi).1 (hYc i hi).2.1 hk, add_zero]

theorem can52_rowsOf (s : String) : Can52 (rowsOf 52 s) := by
  have hs : (rowsOf 52 s).size = 52 := by unfold CFSG.F3.Native.rowsOf; simp
  refine can52_iff.2 ⟨hs, fun i hi => ?_⟩
  have e : (rowsOf 52 s)[i]! =
      V.ofFn 52 fun j => (decodeEntries s).toArray[i * 52 + j]?.getD 0 := by
    unfold CFSG.F3.Native.rowsOf
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  rw [e]
  refine canon52_of_val (V.wf_ofFn _ _) fun k hk => ?_
  rw [V.val_ofFn, if_neg (by omega)]

theorem toMat52_mul {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) :
    toMat 52 (mul 52 X Y) = toMat 52 X * toMat 52 Y :=
  toMat_mul (canonM_spec hX).1 (RowsWF.of_canonM hX) (RowsWF.of_canonM hY)

theorem mul52_assoc {X Y Z : Array V} (hX : Can52 X) (hY : Can52 Y) (hZ : Can52 Z) :
    mul 52 (mul 52 X Y) Z = mul 52 X (mul 52 Y Z) :=
  eq_of_canonM (can52_mul (can52_mul hX hY) hZ) (can52_mul hX (can52_mul hY hZ)) (by
    rw [toMat52_mul (can52_mul hX hY) hZ, toMat52_mul hX hY, toMat52_mul hX (can52_mul hY hZ),
      toMat52_mul hY hZ, Matrix.mul_assoc])

theorem mul52_one {X : Array V} (hX : Can52 X) : mul 52 X (idM 52) = X :=
  eq_of_canonM (can52_mul hX can52_idM) hX (by
    rw [toMat52_mul hX can52_idM, toMat_idM, Matrix.mul_one])

theorem one_mul52 {X : Array V} (hX : Can52 X) : mul 52 (idM 52) X = X :=
  eq_of_canonM (can52_mul can52_idM hX) hX (by
    rw [toMat52_mul can52_idM hX, toMat_idM, Matrix.one_mul])

theorem mul52_comm_of_inv {X Y : Array V} (hX : Can52 X) (hY : Can52 Y)
    (h : mul 52 X Y = idM 52) : mul 52 Y X = idM 52 := by
  apply eq_of_canonM (can52_mul hY hX) can52_idM
  have h' := congrArg (toMat 52) h
  rw [toMat52_mul hX hY, toMat_idM] at h'
  rw [toMat52_mul hY hX, toMat_idM]
  exact (Matrix.mul_eq_one_comm_of_card_eq (Fin 52) (Fin 52) (ZMod 3) rfl).1 h'

theorem inv_unique52 {X Y Z : Array V} (hX : Can52 X) (hY : Can52 Y) (hZ : Can52 Z)
    (h1 : mul 52 X Y = idM 52) (h2 : mul 52 X Z = idM 52) : Y = Z := by
  have h3 := mul52_comm_of_inv hX hY h1
  calc Y = mul 52 Y (idM 52) := (mul52_one hY).symm
    _ = mul 52 Y (mul 52 X Z) := by rw [h2]
    _ = mul 52 (mul 52 Y X) Z := (mul52_assoc hY hX hZ).symm
    _ = Z := by rw [h3, one_mul52 hZ]

@[expose] def pk52 (X : Array V) : ℕ :=
  enc 52 (fun i => X[i]!.p) 52 + 2 ^ 2704 * enc 52 (fun i => X[i]!.m) 52

theorem planeMask_eq : planeMask = 2 ^ 2704 - 1 := by
  show (1 <<< 2704) - 1 = 2 ^ 2704 - 1
  rw [Nat.one_shiftLeft]

theorem rowF_eq : rowF = 2 ^ 52 - 1 := by
  show (1 <<< 52) - 1 = 2 ^ 52 - 1
  rw [Nat.one_shiftLeft]

private theorem can52_p_lt {X : Array V} (hX : Can52 X) {i : ℕ} (hi : i < 52) :
    X[i]!.p < 2 ^ 52 := ((can52_iff.1 hX).2 i hi).1

private theorem can52_m_lt {X : Array V} (hX : Can52 X) {i : ℕ} (hi : i < 52) :
    X[i]!.m < 2 ^ 52 := ((can52_iff.1 hX).2 i hi).2.1

private theorem can52_and {X : Array V} (hX : Can52 X) {i : ℕ} (hi : i < 52) :
    X[i]!.p &&& X[i]!.m = 0 := ((can52_iff.1 hX).2 i hi).2.2

private theorem enc_p_lt {X : Array V} (hX : Can52 X) :
    enc 52 (fun i => X[i]!.p) 52 < 2 ^ 2704 :=
  enc_lt fun _ hi => can52_p_lt hX hi

private theorem enc_m_lt {X : Array V} (hX : Can52 X) :
    enc 52 (fun i => X[i]!.m) 52 < 2 ^ 2704 :=
  enc_lt fun _ hi => can52_m_lt hX hi

private theorem testBit_eq_fd {w x i j : ℕ} (hj : j < w) :
    x.testBit (w * i + j) = (fd w x i).testBit j := by
  unfold fd
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hj, Nat.add_comm]

private theorem testBit_enc {w len : ℕ} {f : ℕ → ℕ} (hf : ∀ i < len, f i < 2 ^ w) {i j : ℕ}
    (hi : i < len) (hj : j < w) : (enc w f len).testBit (w * i + j) = (f i).testBit j := by
  rw [testBit_eq_fd hj, fd_enc hf hi]

private theorem add_mul_lt {a c m n : ℕ} (ha : a < 2 ^ m) (hc : c < 2 ^ n) :
    a + 2 ^ m * c < 2 ^ (m + n) := by
  calc a + 2 ^ m * c < 2 ^ m + 2 ^ m * c := Nat.add_lt_add_right ha _
    _ = 2 ^ m * (c + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ 2 ^ m * 2 ^ n := Nat.mul_le_mul_left _ hc
    _ = 2 ^ (m + n) := (Nat.pow_add 2 m n).symm

private theorem div_lt_of_lt_pow_add {N m n : ℕ} (h : N < 2 ^ (m + n)) : N / 2 ^ m < 2 ^ n := by
  refine (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m)).2 ?_
  rw [← Nat.pow_add, Nat.add_comm]
  exact h

theorem pk52_mod {X : Array V} (hX : Can52 X) : pk52 X % 2 ^ 2704 = enc 52 (fun i => X[i]!.p) 52 := by
  unfold pk52
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (enc_p_lt hX)]

theorem pk52_div {X : Array V} (hX : Can52 X) : pk52 X / 2 ^ 2704 = enc 52 (fun i => X[i]!.m) 52 := by
  unfold pk52
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 2704), Nat.div_eq_of_lt (enc_p_lt hX),
    Nat.zero_add]

theorem pk52_lt {X : Array V} (hX : Can52 X) : pk52 X < 2 ^ 5408 := by
  have h := add_mul_lt (enc_p_lt hX) (enc_m_lt hX)
  exact h

theorem testBit_pk52_p {X : Array V} (hX : Can52 X) {i j : ℕ} (hi : i < 52) (hj : j < 52) :
    (pk52 X).testBit (52 * i + j) = X[i]!.p.testBit j := by
  have e : pk52 X = 2 ^ 2704 * enc 52 (fun i => X[i]!.m) 52 + enc 52 (fun i => X[i]!.p) 52 :=
    Nat.add_comm _ _
  rw [e, Nat.testBit_two_pow_mul_add _ (enc_p_lt hX), if_pos (by omega)]
  exact testBit_enc (fun _ hi => can52_p_lt hX hi) hi hj

theorem testBit_pk52_m {X : Array V} (hX : Can52 X) {i j : ℕ} (hi : i < 52) (hj : j < 52) :
    (pk52 X).testBit (2704 + (52 * i + j)) = X[i]!.m.testBit j := by
  have e : pk52 X = 2 ^ 2704 * enc 52 (fun i => X[i]!.m) 52 + enc 52 (fun i => X[i]!.p) 52 :=
    Nat.add_comm _ _
  rw [e, Nat.testBit_two_pow_mul_add _ (enc_p_lt hX), if_neg (by omega), Nat.add_sub_cancel_left]
  exact testBit_enc (fun _ hi => can52_m_lt hX hi) hi hj

theorem pk52_inj {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) (h : pk52 X = pk52 Y) : X = Y := by
  have hp : enc 52 (fun i => X[i]!.p) 52 = enc 52 (fun i => Y[i]!.p) 52 := by
    rw [← pk52_mod hX, ← pk52_mod hY, h]
  have hm : enc 52 (fun i => X[i]!.m) 52 = enc 52 (fun i => Y[i]!.m) 52 := by
    rw [← pk52_div hX, ← pk52_div hY, h]
  obtain ⟨hXs, -⟩ := can52_iff.1 hX
  obtain ⟨hYs, -⟩ := can52_iff.1 hY
  apply Array.ext (by rw [hXs, hYs])
  intro i hi hi'
  have hi52 : i < 52 := by omega
  have e1 : X[i]!.p = Y[i]!.p := by
    have := congrArg (fun n => fd 52 n i) hp
    simpa only [fd_enc (fun _ hj => can52_p_lt hX hj) hi52,
      fd_enc (fun _ hj => can52_p_lt hY hj) hi52] using this
  have e2 : X[i]!.m = Y[i]!.m := by
    have := congrArg (fun n => fd 52 n i) hm
    simpa only [fd_enc (fun _ hj => can52_m_lt hX hj) hi52,
      fd_enc (fun _ hj => can52_m_lt hY hj) hi52] using this
  rw [getElem!_pos X i hi] at e1 e2
  rw [getElem!_pos Y i hi'] at e1 e2
  cases hx : X[i]
  cases hy : Y[i]
  rw [hx, hy] at e1 e2
  simp only at e1 e2
  rw [e1, e2]

private theorem land_two_pow_sub_one (x n : ℕ) : Nat.land x (2 ^ n - 1) = x % 2 ^ n :=
  Nat.and_two_pow_sub_one_eq_mod x n

private theorem land_planeMask (N : ℕ) : Nat.land N planeMask = N % 2 ^ 2704 := by
  rw [planeMask_eq, land_two_pow_sub_one]

private theorem wfS_iff {N : ℕ} :
    wfS N = true ↔ N < 2 ^ 5408 ∧ (N % 2 ^ 2704) &&& (N / 2 ^ 2704) = 0 := by
  have e1 : Nat.shiftLeft 1 5408 = 2 ^ 5408 := Nat.one_shiftLeft 5408
  have e3 : Nat.shiftRight N 2704 = N / 2 ^ 2704 := Nat.shiftRight_eq_div_pow N 2704
  unfold wfS
  rw [letB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, e1, land_planeMask, e3]
  exact Iff.rfl

theorem wfS_pk52 {X : Array V} (hX : Can52 X) : wfS (pk52 X) = true := by
  rw [wfS_iff, pk52_mod hX, pk52_div hX]
  refine ⟨pk52_lt hX, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hn : n < 2704
  · obtain ⟨i, j, hi, hj, rfl⟩ : ∃ i j, i < 52 ∧ j < 52 ∧ n = 52 * i + j :=
      ⟨n / 52, n % 52, by omega, by omega, by omega⟩
    rw [testBit_enc (fun _ hi => can52_p_lt hX hi) hi hj,
      testBit_enc (fun _ hi => can52_m_lt hX hi) hi hj, ← Nat.testBit_and, can52_and hX hi,
      Nat.zero_testBit]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (enc_p_lt hX)
      (Nat.pow_le_pow_right (by norm_num) (by omega))), Bool.false_and]

theorem exists_pk52 {N : ℕ} (h : wfS N = true) : ∃ X : Array V, Can52 X ∧ pk52 X = N := by
  obtain ⟨hlt, hand⟩ := wfS_iff.1 h
  have ha_lt : N % 2 ^ 2704 < 2 ^ 2704 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hc_lt : N / 2 ^ 2704 < 2 ^ 2704 := div_lt_of_lt_pow_add hlt
  let X : Array V := Array.ofFn (n := 52) fun i =>
    ⟨fd 52 (N % 2 ^ 2704) i.val, fd 52 (N / 2 ^ 2704) i.val⟩
  have hXi : ∀ i < 52, X[i]! = ⟨fd 52 (N % 2 ^ 2704) i, fd 52 (N / 2 ^ 2704) i⟩ := by
    intro i hi
    show (Array.ofFn _)[i]! = _
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have hcan : Can52 X := by
    refine can52_iff.2 ⟨by simp [X], fun i hi => ?_⟩
    rw [hXi i hi]
    refine ⟨fd_lt _ _ _, fd_lt _ _ _, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hj : j < 52
    · rw [← testBit_eq_fd hj, ← testBit_eq_fd hj, ← Nat.testBit_and, hand, Nat.zero_testBit]
    · rw [Nat.testBit_lt_two_pow ((fd_lt 52 (N % 2 ^ 2704) i).trans_le
        (Nat.pow_le_pow_right (by norm_num) (by omega))), Bool.false_and]
  refine ⟨X, hcan, ?_⟩
  unfold pk52
  rw [enc_congr (f := fun i => X[i]!.p) (g := fd 52 (N % 2 ^ 2704)) (fun i hi => by rw [hXi i hi]),
    enc_congr (f := fun i => X[i]!.m) (g := fd 52 (N / 2 ^ 2704)) (fun i hi => by rw [hXi i hi]),
    enc_fd (w := 52) (len := 52) ha_lt, enc_fd (w := 52) (len := 52) hc_lt]
  exact Nat.mod_add_div N (2 ^ 2704)

private theorem enc_one_mul (w n : ℕ) :
    enc w (fun _ => 1) n * (2 ^ w - 1) + 1 = 2 ^ (w * n) := by
  induction n with
  | zero => simp [enc_zero]
  | succ n ih =>
    obtain ⟨c, hc⟩ : ∃ c, 2 ^ w = c + 1 := ⟨2 ^ w - 1, by have := Nat.two_pow_pos w; omega⟩
    have e1 : w * (n + 1) = w * n + w := Nat.mul_succ w n
    have e : 2 ^ (w * (n + 1)) = 2 ^ (w * n) * (c + 1) := by rw [e1, Nat.pow_add, hc]
    rw [e, hc, Nat.add_sub_cancel]
    rw [hc, Nat.add_sub_cancel] at ih
    simp only [enc_succ, Nat.one_mul]
    nlinarith [ih]

private theorem enc_pow_eq (w n : ℕ) :
    enc w (fun i => 2 ^ i) n = enc (w + 1) (fun _ => 1) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : (w + 1) * n = n + w * n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    simp only [enc_succ, Nat.one_mul, ih, e, Nat.pow_add]

private theorem enc_const_zero (w n : ℕ) : enc w (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [enc_succ, ih, Nat.zero_mul, Nat.add_zero]

theorem rowR_eq : rowR = enc 52 (fun _ => 1) 52 := by
  have h := enc_one_mul 52 52
  show planeMask / rowF = _
  rw [planeMask_eq, rowF_eq]
  refine Nat.div_eq_of_eq_mul_left ?_ ?_
  · norm_num
  · exact Nat.sub_eq_of_eq_add h.symm

theorem idS_eq : idS = pk52 (idM 52) := by
  have h := enc_one_mul 53 52
  have e1 : idS = (2 ^ 2756 - 1) / (2 ^ 53 - 1) := by
    show ((1 <<< 2756) - 1) / ((1 <<< 53) - 1) = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
  have e2 : (2 ^ 2756 - 1) / (2 ^ 53 - 1) = enc 53 (fun _ => 1) 52 := by
    refine Nat.div_eq_of_eq_mul_left ?_ ?_
    · norm_num
    · exact Nat.sub_eq_of_eq_add h.symm
  have hi : ∀ i < 52, (idM 52)[i]! = ⟨1 <<< i, 0⟩ := by
    intro i hi
    unfold CFSG.F3.Native.idM
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have e3 : pk52 (idM 52) = enc 53 (fun _ => 1) 52 := by
    unfold pk52
    rw [enc_congr (f := fun i => (idM 52)[i]!.p) (g := fun i => 2 ^ i)
        (fun i hi' => by simp only [hi i hi', Nat.one_shiftLeft]),
      enc_congr (f := fun i => (idM 52)[i]!.m) (g := fun _ => 0)
        (fun i hi' => by simp only [hi i hi']),
      enc_pow_eq, enc_const_zero, Nat.mul_zero, Nat.add_zero]
  rw [e1, e2, e3]

theorem negS_pk52 {X : Array V} (hX : Can52 X) : negS (pk52 X) = pk52 (CFSG.F3.Native.negM X) := by
  have hs := (can52_iff.1 hX).1
  have e1 : Nat.shiftRight (pk52 X) 2704 = enc 52 (fun i => X[i]!.m) 52 :=
    (Nat.shiftRight_eq_div_pow _ _).trans (pk52_div hX)
  have e2 : Nat.land (pk52 X) planeMask = enc 52 (fun i => X[i]!.p) 52 := by
    rw [land_planeMask]; exact pk52_mod hX
  have hn : ∀ i < 52, (CFSG.F3.Native.negM X)[i]! = (X[i]!).neg := by
    intro i hi
    have hi' : i < X.size := by omega
    unfold CFSG.F3.Native.negM
    rw [getElem!_pos _ i (by simpa using hi'), Array.getElem_map, getElem!_pos X i hi']
  unfold negS
  rw [letN_eq, e1, e2]
  show enc 52 (fun i => X[i]!.m) 52 ||| (enc 52 (fun i => X[i]!.p) 52 <<< 2704) = _
  rw [lor_shiftLeft_eq_add (enc_m_lt hX)]
  unfold pk52
  rw [enc_congr (f := fun i => (CFSG.F3.Native.negM X)[i]!.p) (g := fun i => X[i]!.m)
      (fun i hi' => by simp only [hn i hi', V.neg]),
    enc_congr (f := fun i => (CFSG.F3.Native.negM X)[i]!.m) (g := fun i => X[i]!.p)
      (fun i hi' => by simp only [hn i hi', V.neg]),
    Nat.mul_comm]

private theorem eqM_self {X : Array V} (h : X.size = 52) : eqM 52 X X = true := by
  unfold eqM
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.all_eq_finRange_all, List.all_eq_true]
  refine ⟨⟨by simp [h], by simp [h]⟩, fun i _ => ?_⟩
  simp [V.beq]

theorem beq_pk52 {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) :
    Nat.beq (pk52 X) (pk52 Y) = eqM 52 X Y := by
  rw [Bool.eq_iff_iff, Nat.beq_eq]
  constructor
  · intro h
    have hXY : X = Y := pk52_inj hX hY h
    subst hXY
    exact eqM_self (can52_iff.1 hX).1
  · intro h
    have hall : ∀ i < 52, (X[i]!).beq (Y[i]!) = true := by
      intro i hi
      unfold eqM at h
      rw [Bool.and_eq_true, Bool.and_eq_true, Nat.all_eq_finRange_all, List.all_eq_true] at h
      exact h.2 ⟨i, hi⟩ (List.mem_finRange _)
    unfold pk52
    rw [enc_congr (f := fun i => X[i]!.p) (g := fun i => Y[i]!.p)
        (fun i hi => (V.beq_iff.1 (hall i hi)).1),
      enc_congr (f := fun i => X[i]!.m) (g := fun i => Y[i]!.m)
        (fun i hi => (V.beq_iff.1 (hall i hi)).2)]

end CFSG.KS.PK

end
