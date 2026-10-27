module

public import CFSG.Certificates.Kernel.SporSch.LySevBfs
import CFSG.Certificates.Kernel.SporSch.LyLoop
import CFSG.Certificates.Kernel.SporSch.LySevMat

public section

namespace CFSG.KS.SporSch.LySvC

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySev CFSG.KS.SporSch.LyLoop CFSG.KS.SporSch.LyM
open CFSG.KS.SporSch.LySvB
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native

@[expose] noncomputable def qmB (n : Nat) : Nat :=
  foldN n (fun s acc => Nat.lor acc (Nat.shiftLeft (nat_lit 255) (Nat.mul (nat_lit 20) s)))
    (nat_lit 0)

@[expose] def laneSum (v : Nat → Nat) (n : Nat) : Nat := ∑ L ∈ Finset.range n, v L * 2 ^ (20 * L)

theorem lane_lt {v : Nat → Nat} : ∀ {n}, (∀ L < n, v L < 2 ^ 20) → laneSum v n < 2 ^ (20 * n)
  | 0, _ => by simp [laneSum]
  | n + 1, h => by
    unfold laneSum
    rw [Finset.sum_range_succ]
    have h1 := lane_lt (n := n) fun L hL => h L (by omega)
    unfold laneSum at h1
    have h2 := h n (by omega)
    have : v n * 2 ^ (20 * n) ≤ (2 ^ 20 - 1) * 2 ^ (20 * n) := Nat.mul_le_mul_right _ (by omega)
    have e : 2 ^ (20 * (n + 1)) = 2 ^ 20 * 2 ^ (20 * n) := by rw [← Nat.pow_add]; ring_nf
    rw [e]
    have : (2 ^ 20 - 1) * 2 ^ (20 * n) = 2 ^ 20 * 2 ^ (20 * n) - 2 ^ (20 * n) := by
      rw [Nat.sub_mul, Nat.one_mul]
    have hp : 2 ^ (20 * n) ≤ 2 ^ 20 * 2 ^ (20 * n) := Nat.le_mul_of_pos_left _ (by norm_num)
    omega

theorem lane_get {v : Nat → Nat} : ∀ {n}, (∀ L < n, v L < 2 ^ 20) →
    ∀ L < n, laneSum v n / 2 ^ (20 * L) % 2 ^ 20 = v L
  | 0, _ => fun L hL => absurd hL (Nat.not_lt_zero L)
  | n + 1, h => by
    intro L hL
    have hA := lane_lt (n := n) fun L hL => h L (by omega)
    have e : laneSum v (n + 1) = laneSum v n + v n * 2 ^ (20 * n) := by
      unfold laneSum
      rw [Finset.sum_range_succ]
    rw [e]
    rcases Nat.lt_or_ge L n with hLn | hLn
    · have hd : 2 ^ (20 * n) = 2 ^ (20 * L) * 2 ^ 20 * 2 ^ (20 * (n - L - 1)) := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        congr 1
        omega
      have key : laneSum v n + v n * 2 ^ (20 * n) =
          laneSum v n + 2 ^ (20 * L) * (2 ^ 20 * (v n * 2 ^ (20 * (n - L - 1)))) := by
        rw [hd]
        ring
      rw [key, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]
      exact lane_get (n := n) (fun L hL => h L (by omega)) L hLn
    · have : L = n := by omega
      subst this
      rw [Nat.mul_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hA,
        Nat.zero_add, Nat.mod_eq_of_lt (h L (by omega))]

theorem lane_testBit (X L r : Nat) (hr : r < 20) :
    X.testBit (20 * L + r) = (X / 2 ^ (20 * L) % 2 ^ 20).testBit r := by
  rw [testBit_ent]
  simp [hr, Nat.add_comm]

theorem lane_ext {X Y n : Nat} (hX : X < 2 ^ (20 * n)) (hY : Y < 2 ^ (20 * n))
    (h : ∀ L < n, X / 2 ^ (20 * L) % 2 ^ 20 = Y / 2 ^ (20 * L) % 2 ^ 20) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 20 * n
  · have e : b = 20 * (b / 20) + b % 20 := (Nat.div_add_mod b 20).symm
    rw [e, lane_testBit X _ _ (Nat.mod_lt _ (by norm_num)), lane_testBit Y _ _ (Nat.mod_lt _ (by norm_num)),
      h _ (by omega)]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hY (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem lane_repr {X n : Nat} (hX : X < 2 ^ (20 * n)) :
    X = laneSum (fun L => X / 2 ^ (20 * L) % 2 ^ 20) n :=
  lane_ext hX (lane_lt fun L _ => Nat.mod_lt _ (by norm_num)) fun L hL =>
    (lane_get (v := fun L => X / 2 ^ (20 * L) % 2 ^ 20) (fun L _ => Nat.mod_lt _ (by norm_num)) L hL).symm

theorem laneSum_add (u v : Nat → Nat) (n : Nat) :
    laneSum u n + laneSum v n = laneSum (fun L => u L + v L) n := by
  unfold laneSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun L _ => ?_
  ring

theorem laneSum_smul (k : Nat) (v : Nat → Nat) (n : Nat) :
    k * laneSum v n = laneSum (fun L => k * v L) n := by
  unfold laneSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  ring

theorem laneSum_comb (x : Nat → Nat) (V : Nat → Nat → Nat) (m n : Nat) :
    ∑ t ∈ Finset.range m, x t * laneSum (V t) n = laneSum (fun L => ∑ t ∈ Finset.range m, x t * V t L) n := by
  unfold laneSum
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun L _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem qmB_place (n : Nat) : qmB n = CFSG.KS.SporSch.LyK.placeF (fun _ => 255) (fun s => 20 * s) n := by
  unfold qmB CFSG.KS.SporSch.LyK.placeF
  rw [foldN_eqP]
  rfl

theorem qmB_lane {n L : Nat} (hL : L < n) : qmB n / 2 ^ (20 * L) % 2 ^ 20 = 255 := by
  rw [qmB_place]
  exact place_fld (w := 20) (by norm_num) (fun _ _ => by norm_num) hL

theorem qmB_lt (n : Nat) : qmB n < 2 ^ (20 * n) := by
  rw [qmB_place]
  exact CFSG.KS.SporSch.LySvM.placeF_lt (w := 8) n (fun _ _ => by norm_num) fun p hp => by omega

theorem shift_mask {w : Nat → Nat} {n : Nat} (hw : ∀ L < n, w L < 2 ^ 18) :
    Nat.land (Nat.shiftRight (laneSum w n) 10) (qmB n) = laneSum (fun L => w L / 1024) n := by
  have hw20 : ∀ L < n, w L < 2 ^ 20 := fun L hL => Nat.lt_of_lt_of_le (hw L hL) (by norm_num)
  have hq : ∀ L < n, w L / 1024 < 2 ^ 20 := fun L hL => by have := hw L hL; omega
  refine lane_ext (Nat.lt_of_le_of_lt Nat.and_le_right (qmB_lt n)) (lane_lt hq) fun L hL => ?_
  rw [lane_get hq L hL]
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 20
  · rw [← lane_testBit _ _ _ hr]
    change ((laneSum w n >>> 10) &&& qmB n).testBit (20 * L + r) = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, lane_testBit _ _ _ hr, qmB_lane hL]
    have h255 : (255 : Nat) = 2 ^ 8 - 1 := rfl
    rw [h255, Nat.testBit_two_pow_sub_one]
    by_cases hr8 : r < 8
    · have e : 10 + (20 * L + r) = 20 * L + (r + 10) := by omega
      rw [e, lane_testBit _ _ _ (by omega), lane_get hw20 L hL, decide_eq_true hr8, Bool.and_true,
        ← Nat.testBit_div_two_pow]
    · rw [decide_eq_false hr8, Bool.and_false]
      symm
      apply Nat.testBit_lt_two_pow
      have := hw L hL
      calc w L / 1024 < 2 ^ 8 := by omega
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
      (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hq L hL) (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem red5_eq {u : Nat → Nat} {n : Nat} (hu : ∀ L < n, u L < 1024) :
    red5 (qmB n) (laneSum u n) = laneSum (fun L => u L % 5) n := by
  unfold red5
  have h205 : Nat.mul (laneSum u n) (nat_lit 205) = laneSum (fun L => 205 * u L) n := by
    rw [← laneSum_smul]
    exact Nat.mul_comm _ _
  rw [h205, shift_mask (fun L hL => by have := hu L hL; omega)]
  have hsplit : laneSum u n = laneSum (fun L => u L % 5) n + laneSum (fun L => 5 * (205 * u L / 1024)) n := by
    rw [laneSum_add]
    unfold laneSum
    refine Finset.sum_congr rfl fun L hL => ?_
    have := hu L (Finset.mem_range.1 hL)
    refine congrArg (· * 2 ^ (20 * L)) ?_
    dsimp only
    omega
  change laneSum u n - 5 * laneSum (fun L => 205 * u L / 1024) n = _
  rw [laneSum_smul, hsplit]
  exact Nat.add_sub_cancel _ _

theorem pack49_place (Y b : Nat) : pack49 Y b = CFSG.KS.SporSch.LyK.placeF
    (fun t => fld(Y, Nat.add b (Nat.mul (nat_lit 20) t), nat_lit 7)) (fun t => 3 * t) 49 := by
  unfold pack49 CFSG.KS.SporSch.LyK.placeF
  rw [foldN_eqP]
  rfl

theorem d3_pack49 (Y b : Nat) {t : Nat} (ht : t < 49) :
    d3 (pack49 Y b) t = fld(Y, Nat.add b (Nat.mul (nat_lit 20) t), nat_lit 7) := by
  rw [d3_eq, pack49_place]
  exact place_fld (w := 3) (by norm_num) (fun r _ => Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)) ht

theorem fld7_eq (Y o : Nat) : fld(Y, o, nat_lit 7) = Y / 2 ^ o % 8 := by
  change (Y >>> o) &&& (2 ^ 3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fldK_eq (Y o : Nat) : fld(Y, o, 1048575) = Y / 2 ^ o % 2 ^ 20 := by
  change (Y >>> o) &&& (2 ^ 20 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem sum77 (f : Nat → ZMod 5) :
    ∑ t ∈ Finset.range 49, f t = ∑ m ∈ Finset.range 7, ∑ l ∈ Finset.range 7, f (7 * m + l) := by
  have : ∀ a, ∑ t ∈ Finset.range (7 * a), f t = ∑ m ∈ Finset.range a, ∑ l ∈ Finset.range 7, f (7 * m + l) := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih,
        Finset.sum_range_succ (fun m => ∑ l ∈ Finset.range 7, f (7 * m + l))]
  exact this 7

theorem mul7_ent (X Y : Array Nat) {s : Nat} (hs : s < 49) :
    (mul7 X Y)[s]! = (∑ l ∈ Finset.range 7, X[7 * (s / 7) + l]! * Y[7 * l + s % 7]!) % 5 := by
  unfold mul7
  rw [CFSG.KS.SporSch.LyM.ofFn_get! _ hs]
  dsimp only
  rw [fold_sum]

theorem conj_ent (A X B : Array Nat) {s : Nat} (hs : s < 49) :
    (mul7 (mul7 A X) B)[s]! = (∑ l ∈ Finset.range 7,
      ((∑ m ∈ Finset.range 7, A[7 * (s / 7) + m]! * X[7 * m + l]!) % 5) * B[7 * l + s % 7]!) % 5 := by
  rw [mul7_ent _ _ hs]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun l hl => ?_)
  have hl7 := Finset.mem_range.1 hl
  rw [mul7_ent _ _ (by omega)]
  have e1 : (7 * (s / 7) + l) / 7 = s / 7 := by omega
  have e2 : (7 * (s / 7) + l) % 7 = l := by omega
  rw [e1, e2]

theorem conj_eq {kg j QM x : Nat} {KC : Nat → Nat} {A B : Array Nat} (hj : j < kg)
    (hK : ∀ t < 49, ∀ s < 49, fld(KC t, 980 * j + 20 * s, 1048575) =
      A[7 * (s / 7) + t / 7]! * B[7 * (t % 7) + s % 7]! % 5)
    (hKl : ∀ t < 49, ∀ L < 49 * kg, KC t / 2 ^ (20 * L) % 2 ^ 20 < 5)
    (hKb : ∀ t < 49, KC t < 2 ^ (980 * kg)) (hQM : QM = qmB (49 * kg))
    (hx : ∀ t < 49, d3 x t < 5) :
    mul7 (mul7 A (dec49B x)) B = dec49B (pack49 (imgs KC QM x) (Nat.mul 980 j)) ∧
      ∀ t < 49, d3 (pack49 (imgs KC QM x) (Nat.mul 980 j)) t < 5 := by
  set n := 49 * kg with hn
  have hKr : ∀ t < 49, KC t = laneSum (fun L => KC t / 2 ^ (20 * L) % 2 ^ 20) n := fun t ht =>
    lane_repr (by rw [hn, ← Nat.mul_assoc]; exact hKb t ht)
  let u := fun L => ∑ t ∈ Finset.range 49, d3 x t * (KC t / 2 ^ (20 * L) % 2 ^ 20)
  have hsum : foldN (nat_lit 49) (fun t acc => Nat.add acc (Nat.mul (d3 x t) (KC t))) (nat_lit 0) =
      laneSum u n := by
    rw [foldN_eqP, foldr_sum (fun t => Nat.mul (d3 x t) (KC t)) 49 0, Nat.zero_add]
    rw [← laneSum_comb]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [← hKr t (Finset.mem_range.1 ht)]
    rfl
  have hu : ∀ L < n, u L < 1024 := by
    intro L hL
    have : u L ≤ ∑ t ∈ Finset.range 49, 4 * 4 := Finset.sum_le_sum fun t ht => by
      have h1 := hx t (Finset.mem_range.1 ht)
      have h2 := hKl t (Finset.mem_range.1 ht) L hL
      exact Nat.mul_le_mul (by omega) (by omega)
    simp at this
    omega
  have himg : imgs KC QM x = laneSum (fun L => u L % 5) n := by
    unfold imgs
    rw [hsum, hQM, red5_eq hu]
  have hu5 : ∀ L < n, u L % 5 < 2 ^ 20 := fun L _ => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have hd : ∀ s < 49, d3 (pack49 (imgs KC QM x) (Nat.mul 980 j)) s = u (49 * j + s) % 5 := by
    intro s hs
    rw [d3_pack49 _ _ hs, fld7_eq]
    have e : Nat.add (Nat.mul 980 j) (Nat.mul 20 s) = 20 * (49 * j + s) := by
      change 980 * j + 20 * s = _
      ring
    rw [e, himg, ← Nat.mod_mod_of_dvd _ (by norm_num : 8 ∣ 2 ^ 20), lane_get hu5 _ (by rw [hn]; nlinarith)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
  refine ⟨CFSG.KS.SporSch.LyK.arr_ext! (by simp [mul7, dec49B]) fun s hs' => ?_,
    fun t ht => by rw [hd t ht]; exact Nat.mod_lt _ (by norm_num)⟩
  have hs : s < 49 := by simpa [mul7] using hs'
  rw [getD49 hs, hd s hs, conj_ent _ _ _ hs]
  · refine eq_of_cast (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) ?_
    rw [ZMod.natCast_mod, ZMod.natCast_mod]
    simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_mod]
    rw [Finset.sum_congr rfl fun l hl => by
      rw [Finset.sum_congr rfl fun m hm => by
        rw [getD49 (by have := Finset.mem_range.1 hm; have := Finset.mem_range.1 hl; omega)]]]
    simp only [u, Nat.cast_sum, Nat.cast_mul]
    rw [sum77]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun l hl => ?_
    have hm7 := Finset.mem_range.1 hm
    have hl7 := Finset.mem_range.1 hl
    have hL : 49 * j + s < n := by rw [hn]; nlinarith
    have hk := hK (7 * m + l) (by omega) s hs
    rw [fldK_eq] at hk
    have e3 : 20 * (49 * j + s) = 980 * j + 20 * s := by ring
    rw [e3, hk]
    have e4 : (7 * m + l) / 7 = m := by omega
    have e5 : (7 * m + l) % 7 = l := by omega
    rw [e4, e5, ZMod.natCast_mod, Nat.cast_mul]
    ring

theorem rowR_lt (T : Nat → Nat) (rw i : Nat) : rowR T rw i < 2 ^ rw := by
  unfold rowR mask
  have e : Nat.sub (Nat.shiftLeft 1 rw) 1 = 2 ^ rw - 1 := by
    change 1 <<< rw - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [e]
  have hp := Nat.two_pow_pos rw
  change _ &&& (2 ^ rw - 1) < _
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)

theorem dec49B_inj {x y : Nat} (hx : x < 2 ^ 147) (hy : y < 2 ^ 147) (h : dec49B x = dec49B y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 147
  · have e : b = 3 * (b / 3) + b % 3 := (Nat.div_add_mod b 3).symm
    have hr : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have ht : b / 3 < 49 := by omega
    have hd := congrArg (fun A : Array Nat => A[b / 3]!) h
    simp only [getD49 ht, d3_eq] at hd
    rw [e, Nat.add_comm, ← Nat.testBit_div_two_pow, ← Nat.testBit_div_two_pow]
    have h8 : ∀ z : Nat, (z / 2 ^ (3 * (b / 3))).testBit (b % 3) =
        (z / 2 ^ (3 * (b / 3)) % 2 ^ 3).testBit (b % 3) := fun z => by
      rw [Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and]
    rw [h8 x, h8 y]
    exact congrArg (fun z => Nat.testBit z (b % 3)) hd
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem cFail_val : cFail = 1048576 := rfl

theorem cStep_eq (ET WT PT : Nat → Nat) (c h Y j cnt : Nat) :
    cStep ET WT PT c h Y j cnt =
      if fld(rowR WT (nat_lit 95) h, Nat.mul (nat_lit 19) j, nat_lit 524287) < cnt then
        (if rowR ET (nat_lit 147) fld(rowR WT (nat_lit 95) h, Nat.mul (nat_lit 19) j, nat_lit 524287) =
            pack49 Y (Nat.mul (nat_lit 980) j) then cnt else cFail)
      else if fld(rowR WT (nat_lit 95) h, Nat.mul (nat_lit 19) j, nat_lit 524287) = cnt ∧ cnt < c ∧
          rowR ET (nat_lit 147) cnt = pack49 Y (Nat.mul (nat_lit 980) j) ∧
          rowR PT (nat_lit 24) cnt = h + 2 ^ 19 * j then cnt + 1
      else cFail := by
  unfold cStep
  have e1 : Nat.shiftLeft j 19 = 2 ^ 19 * j := by
    change j <<< 19 = _
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
  simp only [strictN_eqP, nIf_eqP, bAnd_eqP, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, e1]
  rfl

theorem fld19 (x o : Nat) : fld(x, o, nat_lit 524287) ≤ 524287 := Nat.and_le_right

theorem cStep_absorb (ET WT PT : Nat → Nat) {c : Nat} (hc : c < 524288) (h Y j : Nat) :
    (∀ cnt, cnt ≤ cFail → cnt ≤ cStep ET WT PT c h Y j cnt ∧ cStep ET WT PT c h Y j cnt ≤ cFail) ∧
    cStep ET WT PT c h Y j cFail = cFail := by
  have hw := fld19 (rowR WT 95 h) (Nat.mul 19 j)
  refine ⟨fun cnt hcnt => ?_, ?_⟩
  · rw [cStep_eq]
    rw [cFail_val] at hcnt ⊢
    split_ifs <;> omega
  · rw [cStep_eq, cFail_val]
    split_ifs <;> omega

@[expose] noncomputable def cH (KC : Nat → Nat) (QM : Nat) (ET WT PT : Nat → Nat) (kg c h cnt : Nat) :
    Nat :=
  if h < cnt then (List.range kg).foldl
    (fun cnt j => cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) j cnt) cnt else cnt

theorem cRun_eq (KC : Nat → Nat) (QM : Nat) (ET WT PT : Nat → Nat) (kg c h₀ len cnt : Nat) :
    cRun KC QM ET WT PT kg c h₀ len cnt =
      (List.range len).foldl (fun cnt i => cH KC QM ET WT PT kg c (h₀ + i) cnt) cnt := by
  unfold cRun
  rw [foldUp_eqP]
  congr 1
  funext cnt i
  rw [strictN_eqP, nIf_eqP, strictN_eqP, foldUp_eqP]
  unfold cH
  simp only [Nat.blt_eq]
  rfl

theorem cH_absorb (KC : Nat → Nat) (QM : Nat) (ET WT PT : Nat → Nat) {kg c : Nat} (hc : c < 524288)
    (h : Nat) :
    (∀ cnt, cnt ≤ cFail → cnt ≤ cH KC QM ET WT PT kg c h cnt ∧ cH KC QM ET WT PT kg c h cnt ≤ cFail) ∧
    cH KC QM ET WT PT kg c h cFail = cFail := by
  have hf := fold_absorb (fun j s => cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) j s) cFail
    (fun j => (cStep_absorb ET WT PT hc h _ j).1) (fun j => (cStep_absorb ET WT PT hc h _ j).2)
    (List.range kg)
  refine ⟨fun cnt hcnt => ?_, ?_⟩
  · unfold cH
    split_ifs
    · exact ⟨(hf cnt hcnt).1, (hf cnt hcnt).2.1⟩
    · exact ⟨le_rfl, hcnt⟩
  · unfold cH
    split_ifs
    · exact (hf cFail le_rfl).2.2 rfl
    · rfl

@[expose] def AC (KC : Nat → Nat) (QM : Nat) (ET PT : Nat → Nat) (kg cnt : Nat) : Prop :=
  (∀ i < cnt, ∀ t < 49, d3 (rowR ET 147 i) t < 5) ∧
  (∀ i < cnt, 0 < i → Nat.land (rowR PT 24 i) 524287 < i ∧ Nat.shiftRight (rowR PT 24 i) 19 < kg ∧
    rowR ET 147 i = pack49 (imgs KC QM (rowR ET 147 (Nat.land (rowR PT 24 i) 524287)))
      (Nat.mul 980 (Nat.shiftRight (rowR PT 24 i) 19)))

@[expose] def NC (ET PT : Nat → Nat) (cnt : Nat)
    (s : Std.HashMap (Array Nat) Nat × Array (Array Nat) × Array Nat × Array Nat) : Prop :=
  s.2.1 = (Array.ofFn (n := cnt) fun i => dec49B (rowR ET 147 i.val)) ∧
  (∀ z, s.1.contains z = true ↔ ∃ i < cnt, dec49B (rowR ET 147 i) = z) ∧
  s.2.2.1 = (Array.ofFn (n := cnt) fun i => Nat.land (rowR PT 24 i.val) 524287) ∧
  s.2.2.2 = (Array.ofFn (n := cnt) fun i => Nat.shiftRight (rowR PT 24 i.val) 19)

theorem land19 {h j : Nat} (hh : h < 2 ^ 19) : Nat.land (h + 2 ^ 19 * j) 524287 = h := by
  change (h + 2 ^ 19 * j) &&& (2 ^ 19 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hh]

theorem shr19 {h j : Nat} (hh : h < 2 ^ 19) : Nat.shiftRight (h + 2 ^ 19 * j) 19 = j := by
  change (h + 2 ^ 19 * j) >>> 19 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hh,
    Nat.zero_add]

theorem cstep_sim {kg c QM : Nat} {KC ET WT PT : Nat → Nat} {gens : Array (Array Nat × Array Nat)}
    (hg : gens.size = kg)
    (hconj : ∀ j < kg, ∀ x, (∀ t < 49, d3 x t < 5) →
      mul7 (mul7 gens[j]!.1 (dec49B x)) gens[j]!.2 = dec49B (pack49 (imgs KC QM x) (Nat.mul 980 j)) ∧
      ∀ t < 49, d3 (pack49 (imgs KC QM x) (Nat.mul 980 j)) t < 5)
    (hinj : ∀ a < c, ∀ b < c, rowR ET 147 a = rowR ET 147 b → a = b) (hc : c < 524288)
    {h j cnt : Nat} {s : Std.HashMap (Array Nat) Nat × Array (Array Nat) × Array Nat × Array Nat}
    (hj : j < kg) (hac : AC KC QM ET PT kg cnt) (hnc : NC ET PT cnt s) (hh : h < cnt)
    (hle : cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) j cnt ≤ c) :
    AC KC QM ET PT kg (cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) j cnt) ∧
      cnt ≤ cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) j cnt ∧
      NC ET PT (cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) j cnt)
        (if (!s.1.contains (mul7 (mul7 gens[j]!.1 (dec49B (rowR ET 147 h))) gens[j]!.2)) = true then
          (s.1.insert (mul7 (mul7 gens[j]!.1 (dec49B (rowR ET 147 h))) gens[j]!.2) s.2.1.size,
            s.2.1.push (mul7 (mul7 gens[j]!.1 (dec49B (rowR ET 147 h))) gens[j]!.2),
            s.2.2.1.push h, s.2.2.2.push j)
        else (s.1, s.2.1, s.2.2.1, s.2.2.2)) := by
  obtain ⟨a1, a2⟩ := hac
  obtain ⟨n1, n2, n3, n4⟩ := hnc
  obtain ⟨hy, hyd⟩ := hconj j hj _ (a1 h hh)
  set yv := pack49 (imgs KC QM (rowR ET 147 h)) (Nat.mul 980 j) with hyv
  rw [hy]
  rw [cStep_eq] at hle ⊢
  rw [cFail_val] at hle
  by_cases hw : fld(rowR WT (nat_lit 95) h, Nat.mul (nat_lit 19) j, nat_lit 524287) < cnt
  · rw [if_pos hw] at hle ⊢
    by_cases he : rowR ET (nat_lit 147) fld(rowR WT (nat_lit 95) h, Nat.mul (nat_lit 19) j,
        nat_lit 524287) = yv
    · rw [if_pos he]
      have hcont : s.1.contains (dec49B yv) = true := (n2 _).2 ⟨_, hw, by rw [← he]⟩
      rw [hcont]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ⟨⟨a1, a2⟩, le_rfl, n1, n2, n3, n4⟩
    · rw [if_neg he] at hle
      omega
  · rw [if_neg hw] at hle ⊢
    by_cases hn : fld(rowR WT (nat_lit 95) h, Nat.mul (nat_lit 19) j, nat_lit 524287) = cnt ∧ cnt < c ∧
        rowR ET (nat_lit 147) cnt = yv ∧ rowR PT (nat_lit 24) cnt = h + 2 ^ 19 * j
    · rw [if_pos hn]
      obtain ⟨-, hn1, hn2, hn3⟩ := hn
      have hcont : s.1.contains (dec49B yv) = false := by
        cases e : s.1.contains (dec49B yv)
        · rfl
        · obtain ⟨i, hi, hiz⟩ := (n2 _).1 e
          rw [← hn2] at hiz
          have := hinj i (by omega) cnt hn1 (dec49B_inj (rowR_lt _ _ _) (rowR_lt _ _ _) hiz)
          omega
      rw [hcont]
      simp only [Bool.not_false, ↓reduceIte]
      have hh19 : h < 2 ^ 19 := by omega
      refine ⟨⟨fun i hi t ht => ?_, fun i hi hi0 => ?_⟩, by omega, ?_, fun z => ?_, ?_, ?_⟩
      · rcases Nat.lt_or_ge i cnt with h' | h'
        · exact a1 i h' t ht
        · have : i = cnt := by omega
          subst this
          rw [hn2]
          exact hyd t ht
      · rcases Nat.lt_or_ge i cnt with h' | h'
        · exact a2 i h' hi0
        · have : i = cnt := by omega
          subst this
          rw [hn3, land19 hh19, shr19 hh19, hn2]
          exact ⟨hh, hj, rfl⟩
      · change s.2.1.push (dec49B yv) = _
        rw [n1, ← hn2]
        exact ofFn_push (fun i => dec49B (rowR ET 147 i)) cnt
      · change (s.1.insert (dec49B yv) s.2.1.size).contains z = true ↔ _
        rw [Std.HashMap.contains_insert, Bool.or_eq_true, n2, beq_iff_eq]
        constructor
        · rintro (e | ⟨i, hi, e⟩)
          · exact ⟨cnt, by omega, by rw [hn2, e]⟩
          · exact ⟨i, by omega, e⟩
        · rintro ⟨i, hi, e⟩
          rcases Nat.lt_or_ge i cnt with h' | h'
          · exact Or.inr ⟨i, h', e⟩
          · have : i = cnt := by omega
            subst this
            exact Or.inl (by rw [← e, hn2])
      · change s.2.2.1.push h = _
        have : h = Nat.land (rowR PT 24 cnt) 524287 := by rw [hn3, land19 hh19]
        rw [n3, this]
        exact ofFn_push (fun i => Nat.land (rowR PT 24 i) 524287) cnt
      · change s.2.2.2.push j = _
        have : j = Nat.shiftRight (rowR PT 24 cnt) 19 := by rw [hn3, shr19 hh19]
        rw [n4, this]
        exact ofFn_push (fun i => Nat.shiftRight (rowR PT 24 i) 19) cnt
    · rw [if_neg hn] at hle
      omega

theorem foldl_skipN (f : Nat → Nat → Nat) (hskip : ∀ h st, st ≤ h → f h st = st) :
    ∀ (l : List Nat) (st : Nat), (∀ x ∈ l, st ≤ x) → l.foldl (fun st h => f h st) st = st
  | [], _, _ => rfl
  | x :: l, st, hl => by
    rw [List.foldl_cons, hskip _ _ (hl x List.mem_cons_self)]
    exact foldl_skipN f hskip l st fun y hy => hl y (List.mem_cons_of_mem _ hy)

theorem cbfs_soundL {kg c nS Hh cap QM : Nat} {KC ET WT PT SO SOI C : Nat → Nat} {root : Array Nat}
    {gens : Array (Array Nat × Array Nat)} (hg : gens.size = kg)
    (hK : ∀ j < kg, ∀ t < 49, ∀ s < 49, fld(KC t, 980 * j + 20 * s, 1048575) =
      gens[j]!.1[7 * (s / 7) + t / 7]! * gens[j]!.2[7 * (t % 7) + s % 7]! % 5)
    (hKb : ∀ t < 49, KC t < 2 ^ (980 * kg)) (hQM : QM = qmB (49 * kg))
    (hroot : root = dec49B (rowR ET 147 0)) (hE0 : ∀ t < 49, d3 (rowR ET 147 0) t < 5)
    (hPT0 : rowR PT 24 0 = 0)
    (hsort : ∀ i < c, sortB (fun i => rowR ET 147 i) SO SOI c i = true)
    (hc : c < 524288) (hcap : c ≤ cap) (hcov : c ≤ nS * Hh) (hC0 : C 0 = 1)
    (hrun : ∀ q < nS, cRun KC QM ET WT PT kg c (q * Hh) Hh (C q) = C (q + 1)) (hCn : C nS = c) :
    conjBFS root gens cap = (Array.ofFn (n := c) fun i => dec49B (rowR ET 147 i.val),
        Array.ofFn (n := c) fun i => Nat.land (rowR PT 24 i.val) 524287,
        Array.ofFn (n := c) fun i => Nat.shiftRight (rowR PT 24 i.val) 19) ∧
      conjTreeOK root gens (Array.ofFn (n := c) fun i => dec49B (rowR ET 147 i.val),
        Array.ofFn (n := c) fun i => Nat.land (rowR PT 24 i.val) 524287,
        Array.ofFn (n := c) fun i => Nat.shiftRight (rowR PT 24 i.val) 19) = true := by
  have hKl : ∀ t < 49, ∀ L < 49 * kg, KC t / 2 ^ (20 * L) % 2 ^ 20 < 5 := by
    intro t ht L hL
    have hj : L / 49 < kg := by omega
    have e : 20 * L = 980 * (L / 49) + 20 * (L % 49) := by omega
    have := hK (L / 49) hj t ht (L % 49) (Nat.mod_lt _ (by norm_num))
    rw [fldK_eq, ← e] at this
    rw [this]
    exact Nat.mod_lt _ (by norm_num)
  have hconj : ∀ j < kg, ∀ x, (∀ t < 49, d3 x t < 5) →
      mul7 (mul7 gens[j]!.1 (dec49B x)) gens[j]!.2 = dec49B (pack49 (imgs KC QM x) (Nat.mul 980 j)) ∧
      ∀ t < 49, d3 (pack49 (imgs KC QM x) (Nat.mul 980 j)) t < 5 :=
    fun j hj x hx => conj_eq hj (hK j hj) hKl hKb hQM hx
  have hinj : ∀ a < c, ∀ b < c, rowR ET 147 a = rowR ET 147 b → a = b := sortB_inj hsort
  let cHf := fun h cnt => cH KC QM ET WT PT kg c h cnt
  let stG := fun t => (List.range t).foldl (fun cnt h => cHf h cnt) 1
  have hGs : ∀ t, stG (t + 1) = cHf t (stG t) := by
    intro t
    change (List.range (t + 1)).foldl _ _ = _
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hCq : ∀ q ≤ nS, C q = stG (q * Hh) := by
    intro q
    induction q with
    | zero => intro _; rw [hC0, Nat.zero_mul]; rfl
    | succ q ih =>
      intro hq
      rw [← hrun q (by omega), cRun_eq, ih (by omega)]
      have e := range_splitG (fun h st => cHf h st) 1 (a := q * Hh) (b := (q + 1) * Hh)
        (Nat.mul_le_mul_right Hh (Nat.le_succ q))
      have e2 : (q + 1) * Hh - q * Hh = Hh := by rw [Nat.succ_mul]; omega
      rw [e2, List.range'_eq_map_range, List.foldl_map] at e
      exact e.symm
  set N := nS * Hh with hN
  have hGN : stG N = c := by rw [← hCq nS le_rfl, hCn]
  have hskip1 : ∀ h cnt, cnt ≤ h → cHf h cnt = cnt := by
    intro h cnt hh
    change cH KC QM ET WT PT kg c h cnt = cnt
    unfold cH
    rw [if_neg (by omega)]
  have hskipN : ∀ t, stG (N + t) = stG N := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [← Nat.add_assoc, hGs, ih]
      exact hskip1 _ _ (by omega)
  have habs := fun l s hs => fold_absorb (fun h s => cHf h s) cFail
    (fun h => (cH_absorb KC QM ET WT PT hc h).1) (fun h => (cH_absorb KC QM ET WT PT hc h).2) l s hs
  have h1F : (1 : Nat) ≤ cFail := by rw [cFail_val]; omega
  have hcF : c < cFail := by rw [cFail_val]; omega
  have hGt : ∀ t, stG t ≤ c ∧ stG t ≠ cFail := by
    intro t
    have e : stG (N + t) = (List.range' t N).foldl (fun s x => cHf x s) (stG t) := by
      have := range_splitG (fun h st => cHf h st) 1 (a := t) (b := N + t) (by omega)
      rw [Nat.add_sub_cancel] at this
      exact this
    have hb := habs (List.range t) 1 h1F
    have ha := habs (List.range' t N) (stG t) hb.2.1
    rw [← e, hskipN, hGN] at ha
    exact ⟨ha.1, fun hh => absurd (ha.2.2 hh) (Nat.ne_of_lt hcF)⟩
  have hc1 : 1 ≤ c := by
    have := (habs (List.range N) 1 h1F).1
    change 1 ≤ stG N at this
    rw [hGN] at this
    exact this
  let sI := fun h j => (List.range j).foldl
    (fun cnt j => cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) j cnt) (stG h)
  have hIs : ∀ h j, sI h (j + 1) = cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) j (sI h j) := by
    intro h j
    change (List.range (j + 1)).foldl _ _ = _
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hIk : ∀ h, h < stG h → sI h kg = stG (h + 1) := by
    intro h hh
    rw [hGs]
    change _ = cH KC QM ET WT PT kg c h (stG h)
    unfold cH
    rw [if_pos hh]
  have hIle : ∀ h, h < stG h → ∀ j ≤ kg, sI h j ≤ c ∧ stG h ≤ sI h j := by
    intro h hh j hj
    have habsI := fun l s hs => fold_absorb
      (fun j s => cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) j s) cFail
      (fun j => (cStep_absorb ET WT PT hc h _ j).1) (fun j => (cStep_absorb ET WT PT hc h _ j).2) l s hs
    have e : sI h kg = (List.range' j (kg - j)).foldl
        (fun s x => cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) x s) (sI h j) :=
      range_splitG (fun j s => cStep ET WT PT c h (imgs KC QM (rowR ET 147 h)) j s) (stG h) hj
    have hb := habsI (List.range j) (stG h) (Nat.le_trans (hGt h).1 (Nat.le_of_lt hcF))
    have ha := habsI (List.range' j (kg - j)) (sI h j) hb.2.1
    rw [← e, hIk h hh] at ha
    exact ⟨Nat.le_trans ha.1 (hGt (h + 1)).1, hb.1⟩
  let R := fun t s => AC KC QM ET PT kg (stG t) ∧ NC ET PT (stG t) s
  have hex : ∃ s, conjBFS root gens cap = (s.2.1, s.2.2.1, s.2.2.2) ∧ R cap s := by
    unfold conjBFS
    refine ⟨_, rfl, forIn_range_spec (fun t s => R t s) cap _ _ ?_ ?_⟩
    ·
      change AC KC QM ET PT kg 1 ∧ NC ET PT 1 _
      refine ⟨⟨fun i hi => ?_, fun i hi hi0 => by omega⟩, ?_, fun z => ?_, ?_, ?_⟩
      · have : i = 0 := by omega
        rw [this]
        exact hE0
      · change #[root] = _
        rw [hroot]
        rfl
      · change ((∅ : Std.HashMap (Array Nat) Nat).insert root 0).contains z = true ↔ _
        rw [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false, beq_iff_eq]
        constructor
        · rintro rfl
          exact ⟨0, by omega, hroot.symm⟩
        · rintro ⟨i, hi, e⟩
          have : i = 0 := by omega
          rw [hroot, ← e, this]
      · apply Array.ext
        · simp
        · intro i h1 h2
          have : i = 0 := by simpa using h1
          subst this
          simp [hPT0]
      · apply Array.ext
        · simp
        · intro i h1 h2
          have : i = 0 := by simpa using h1
          subst this
          simp [hPT0]
    ·
      intro h b hh hb
      obtain ⟨hac, hnc⟩ := hb
      have hsz : b.2.1.size = stG h := by rw [hnc.1]; simp
      dsimp only
      split
      · rename_i hlt
        rw [hsz] at hlt
        refine ⟨_, rfl, ?_⟩
        have hx : b.2.1[h]! = dec49B (rowR ET 147 h) := by
          rw [hnc.1]
          exact ofFn_getP (fun i => dec49B (rowR ET 147 i)) hlt
        have hfin : ∀ s, (AC KC QM ET PT kg (sI h gens.size) ∧ NC ET PT (sI h gens.size) s ∧
            stG h ≤ sI h gens.size) → R (h + 1) (s.1, s.2.1, s.2.2.1, s.2.2.2) := by
          intro s hs
          rw [hg, hIk h hlt] at hs
          exact ⟨hs.1, hs.2.1⟩
        refine hfin _ (forIn_range_spec (fun j s => AC KC QM ET PT kg (sI h j) ∧ NC ET PT (sI h j) s ∧
          stG h ≤ sI h j) gens.size _ _ ⟨hac, hnc, le_rfl⟩ ?_)
        intro j s hj hs
        rw [hg] at hj
        obtain ⟨hs1, hs2, hs3⟩ := hs
        refine ⟨_, (apply_ite (fun z => (pure (ForInStep.yield z) : Id _)) _ _ _).symm, ?_⟩
        have hsim := cstep_sim hg hconj hinj hc hj hs1 hs2 (Nat.lt_of_lt_of_le hlt hs3)
          (by rw [← hIs]; exact (hIle h hlt (j + 1) (by omega)).1)
        rw [← hIs] at hsim
        rw [hx]
        exact ⟨hsim.1, hsim.2.2, Nat.le_trans hs3 hsim.2.1⟩
      · rename_i hge
        rw [hsz] at hge
        refine ⟨_, rfl, ?_⟩
        change AC KC QM ET PT kg (stG (h + 1)) ∧ NC ET PT (stG (h + 1)) b
        have e : stG (h + 1) = stG h := by rw [hGs]; exact hskip1 _ _ (by omega)
        rw [e]
        exact ⟨hac, hnc⟩
  obtain ⟨s, hs, hac, hnc⟩ := hex
  have hGc : stG cap = c := by
    rcases Nat.le_total N cap with h1 | h1
    · have := hskipN (cap - N)
      rw [Nat.add_sub_cancel' h1] at this
      rw [this, hGN]
    · have e : stG N = (List.range' cap (N - cap)).foldl (fun s x => cHf x s) (stG cap) :=
        range_splitG (fun h st => cHf h st) 1 h1
      rw [e, foldl_skipN cHf hskip1 _ _ fun x hx => ?_] at hGN
      · exact hGN
      · have := List.mem_range'.1 hx
        have := (hGt cap).1
        omega
  obtain ⟨a1, a2⟩ := hac
  obtain ⟨n1, n2, n3, n4⟩ := hnc
  rw [hGc] at a1 a2 n1 n3 n4
  refine ⟨by rw [hs, n1, n3, n4], ?_⟩
  unfold conjTreeOK
  dsimp only
  simp only [Bool.and_eq_true]
  have hpts : ∀ k < c, (Array.ofFn (n := c) fun i => dec49B (rowR ET 147 i.val))[k]! =
      dec49B (rowR ET 147 k) := fun k hk => ofFn_getP (fun i => dec49B (rowR ET 147 i)) hk
  refine ⟨⟨⟨⟨⟨by simp, by simp⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hpts 0 (by omega), hroot]
    exact beq_self_eq_true _
  · rw [Array.all_eq_true]
    intro i hi
    rw [Array.size_ofFn] at hi
    rw [Array.getElem_ofFn]
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
    refine ⟨by simp [dec49B], fun r hr => ?_⟩
    have hr' : r < 49 := by simpa [dec49B] using hr
    simp only [dec49B, Array.getElem_ofFn]
    exact decide_eq_true (a1 i hi r hr')
  · rw [allIn_iff']
    intro k hk1 hk2
    rw [Array.size_ofFn] at hk2
    have hpar := ofFn_getP (fun i => Nat.land (rowR PT 24 i) 524287) hk2
    have hlab := ofFn_getP (fun i => Nat.shiftRight (rowR PT 24 i) 19) hk2
    obtain ⟨t1, t2, t3⟩ := a2 k hk2 (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [hpar, hlab, hg]
    refine ⟨⟨t1, t2⟩, ?_⟩
    rw [hpts _ (by omega), (hconj _ t2 _ (a1 _ (by omega))).1, hpts k hk2, ← t3]
  · rw [allIn_iff']
    intro k _ hk2
    rw [beq_iff_eq]
    rw [Array.size_ofFn] at hk2 ⊢
    refine index_getD _ (fun a ha b hb e => ?_) hk2
    rw [hpts a ha, hpts b hb] at e
    exact hinj a ha b hb (dec49B_inj (rowR_lt _ _ _) (rowR_lt _ _ _) e)

end CFSG.KS.SporSch.LySvC

end
