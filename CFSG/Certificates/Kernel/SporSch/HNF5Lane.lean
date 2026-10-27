module

public import Certificates.Data.Kernel.SporSch.HNF5Mod
public import Certificates.Data.Kernel.SporSch.HNF5Dig
public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option exponentiation.threshold 2200

namespace CFSG.KS.SporSch.F5Lane

open CFSG.KC.Enum CFSG.KS.SporSch CFSG.KS.SporSch.LyM CFSG.Sporadic.He.Native Finset

theorem lane5_eq (x j : Nat) : lane5 x j = x / 2 ^ (16 * j) % 2 ^ 16 := by
  unfold lane5
  change Nat.land (Nat.shiftRight x (16 * j)) (2 ^ 16 - 1) = _
  exact CFSG.KC.Pack.fld_eq x (16 * j) 16

theorem lane5_lt (x j : Nat) : lane5 x j < 2 ^ 16 := by
  rw [lane5_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos 16)

theorem lane5_zero (j : Nat) : lane5 0 j = 0 := by
  rw [lane5_eq]
  simp

theorem lane5_or_shl {a v j k : Nat} (hv : v < 2 ^ 16) :
    lane5 (Nat.lor a (Nat.shiftLeft v (Nat.mul (nat_lit 16) j))) k =
      if k = j then lane5 a k ||| v else lane5 a k := by
  rw [lane5_eq, lane5_eq]
  change (a ||| v <<< (16 * j)) / 2 ^ (16 * k) % 2 ^ 16 = _
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_ent, Nat.testBit_lor, Nat.testBit_shiftLeft]
  by_cases hkj : k = j
  · subst hkj
    rw [ite_eq_left rfl, Nat.testBit_lor, testBit_ent]
    by_cases hr : r < 16
    · simp [hr]
    · have hv' : v.testBit r = false := Nat.testBit_eq_false_of_lt
        (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hr, hv']
  · rw [ite_eq_right hkj, testBit_ent]
    by_cases hr : r < 16
    · have hz : (decide (r + 16 * k ≥ 16 * j) && v.testBit (r + 16 * k - 16 * j)) = false := by
        by_cases hge : r + 16 * k ≥ 16 * j
        · have hlt : 16 ≤ r + 16 * k - 16 * j := by omega
          have hv' := Nat.testBit_eq_false_of_lt
            (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hlt))
          simp [hv']
        · simp [hge]
      rw [hz, Bool.or_false]
    · simp [hr]

theorem lane5_foldr_or {g : Nat → Nat} (hg : ∀ j, g j < 2 ^ 16) (k : Nat) :
    ∀ (l : List Nat) (a : Nat),
      lane5 (l.foldr (fun j acc => Nat.lor acc (Nat.shiftLeft (g j) (Nat.mul (nat_lit 16) j))) a) k =
        lane5 a k ||| (if k ∈ l then g k else 0)
  | [], a => by simp
  | j :: l, a => by
    rw [List.foldr_cons, lane5_or_shl (hg j), lane5_foldr_or hg k l a]
    by_cases hkj : k = j
    · subst hkj
      rw [ite_eq_left rfl, ite_eq_left List.mem_cons_self]
      split_ifs <;> simp
    · rw [ite_eq_right hkj]
      simp [List.mem_cons, hkj]

theorem lane5_red5 (s : Nat) {k : Nat} (hk : k < 133) : lane5 (red5 s) k = lane5 s k % 5 := by
  unfold red5
  rw [CFSG.KC.Pack.foldN_eq, lane5_foldr_or (g := fun j => Nat.mod (lane5 s j) 5)
    (fun j => Nat.lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)) k, lane5_zero,
    Nat.zero_or, ite_eq_left (List.mem_range.2 hk)]
  rfl

theorem lane5_trRow5 (T : Nat → Nat) (i : Nat) {t : Nat} (ht : t < 133) :
    lane5 (trRow5 T i) t = lane5 (T t) i := by
  unfold trRow5
  rw [CFSG.KC.Pack.foldN_eq, lane5_foldr_or (g := fun j => lane5 (T j) i) (fun j => lane5_lt _ _) t,
    lane5_zero, Nat.zero_or, ite_eq_left (List.mem_range.2 ht)]

theorem lane5_idRow5 (i k : Nat) : lane5 (idRow5 i) k = if k = i then 1 else 0 := by
  have h := lane5_or_shl (a := 0) (v := 1) (j := i) (k := k) (by norm_num)
  have e : Nat.lor 0 (Nat.shiftLeft 1 (Nat.mul (nat_lit 16) i)) =
      Nat.shiftLeft 1 (Nat.mul (nat_lit 16) i) := Nat.zero_or _
  rw [e, lane5_zero, Nat.zero_or] at h
  exact h

theorem idRow5_lt {i : Nat} (hi : i < 133) : idRow5 i < 2 ^ 2128 := by
  unfold idRow5
  change 1 <<< (16 * i) < _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem canon5_lt {x : Nat} (h : canon5 x = true) : x < 2 ^ 2128 := by
  unfold canon5 at h
  have h1 := Nat.eq_of_beq_eq_true ((CFSG.KS.bAnd_iff _ _).1 h).1
  change x >>> 2128 = 0 at h1
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (Nat.two_pow_pos _).ne'
  · exact h1

theorem canon5_lane {x : Nat} (h : canon5 x = true) {j : Nat} (hj : j < 133) : lane5 x j < 5 := by
  unfold canon5 at h
  exact Eq.mp Nat.blt_eq (CFSG.KS.allN_spec ((CFSG.KS.bAnd_iff _ _).1 h).2 j hj)

theorem mod_expand (x : Nat) : ∀ n, x % 2 ^ (16 * n) = ∑ j ∈ range n, lane5 x j * 2 ^ (16 * j)
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    rw [Finset.sum_range_succ, ← mod_expand x n, Nat.mul_succ, Nat.pow_add, Nat.mod_mul, lane5_eq]
    ring

theorem row_expand {x : Nat} (hx : x < 2 ^ 2128) :
    x = ∑ j ∈ range 133, lane5 x j * 2 ^ (16 * j) := by
  rw [← mod_expand x 133, Nat.mod_eq_of_lt (by simpa using hx)]

theorem eq_of_lanes {x y : Nat} (hx : x < 2 ^ 2128) (hy : y < 2 ^ 2128)
    (h : ∀ j < 133, lane5 x j = lane5 y j) : x = y := by
  rw [row_expand hx, row_expand hy]
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]

theorem sum_lt (f : Nat → Nat) : ∀ n, (∀ j < n, f j < 2 ^ 16) →
    ∑ j ∈ range n, f j * 2 ^ (16 * j) < 2 ^ (16 * n)
  | 0, _ => by simp
  | n + 1, hf => by
    rw [Finset.sum_range_succ, Nat.mul_succ, Nat.pow_add]
    have h1 := sum_lt f n fun j hj => hf j (by omega)
    have h2 := hf n (by omega)
    calc _ < 2 ^ (16 * n) + f n * 2 ^ (16 * n) := by omega
      _ = (f n + 1) * 2 ^ (16 * n) := by ring
      _ ≤ 2 ^ 16 * 2 ^ (16 * n) := Nat.mul_le_mul_right _ h2
      _ = _ := by ring

theorem lane_sum (f : Nat → Nat) : ∀ n, (∀ j < n, f j < 2 ^ 16) →
    ∀ k < n, (∑ j ∈ range n, f j * 2 ^ (16 * j)) / 2 ^ (16 * k) % 2 ^ 16 = f k
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, hf, k, hk => by
    rw [Finset.sum_range_succ]
    have hS := sum_lt f n fun j hj => hf j (by omega)
    rcases Nat.lt_or_ge k n with hkn | hkn
    · have e : f n * 2 ^ (16 * n) =
          2 ^ 16 * (2 ^ (16 * (n - k - 1)) * f n) * 2 ^ (16 * k) := by
        have e1 : 2 ^ (16 * n) = 2 ^ (16 * k) * (2 ^ 16 * 2 ^ (16 * (n - k - 1))) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
          congr 1
          omega
        rw [e1]
        ring
      rw [e, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]
      exact lane_sum f n (fun j hj => hf j (by omega)) k hkn
    · obtain rfl : k = n := by omega
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hS, Nat.zero_add,
        Nat.mod_eq_of_lt (hf k (by omega))]

theorem lane_sum5 {f : Nat → Nat} (hf : ∀ t < 133, f t < 2 ^ 16) {k : Nat} (hk : k < 133) :
    lane5 (∑ t ∈ range 133, f t * 2 ^ (16 * t)) k = f k := by
  rw [lane5_eq]
  exact lane_sum f 133 hf k hk

theorem foldr_range_add {F : Nat → Nat → Nat} (h : Nat → Nat) (hF : ∀ j acc, F j acc = acc + h j) :
    ∀ n a, (List.range n).foldr F a = a + ∑ j ∈ range n, h j
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, hF,
      foldr_range_add h hF n, Finset.sum_range_succ]
    ring

theorem vm5_eq (Y : Nat → Nat) (x : Nat) :
    vm5 Y x = red5 (∑ j ∈ range 133, lane5 x j * Y j) := by
  unfold vm5
  rw [strictN_valL, CFSG.KC.Pack.foldN_eq, foldr_range_add (fun j => lane5 x j * Y j), Nat.zero_add]
  intro j acc
  rw [strictN_valL]
  cases h : Nat.beq (lane5 x j) 0
  · rfl
  · rw [Nat.eq_of_beq_eq_true h]
    simp

theorem vm5_lane {Y : Nat → Nat} {x k : Nat} (hY : ∀ j < 133, canon5 (Y j) = true)
    (hx : canon5 x = true) (hk : k < 133) :
    lane5 (vm5 Y x) k = (∑ j ∈ range 133, lane5 x j * lane5 (Y j) k) % 5 := by
  have e : ∑ j ∈ range 133, lane5 x j * Y j =
      ∑ t ∈ range 133, (∑ j ∈ range 133, lane5 x j * lane5 (Y j) t) * 2 ^ (16 * t) := by
    calc ∑ j ∈ range 133, lane5 x j * Y j
        = ∑ j ∈ range 133, ∑ t ∈ range 133, lane5 x j * lane5 (Y j) t * 2 ^ (16 * t) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          conv_lhs => rw [row_expand (canon5_lt (hY j (Finset.mem_range.1 hj)))]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          ring
      _ = ∑ t ∈ range 133, ∑ j ∈ range 133, lane5 x j * lane5 (Y j) t * 2 ^ (16 * t) :=
          Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_mul]
  have hb : ∀ t < 133, ∑ j ∈ range 133, lane5 x j * lane5 (Y j) t < 2 ^ 16 := fun t ht =>
    calc ∑ j ∈ range 133, lane5 x j * lane5 (Y j) t
        ≤ ∑ _j ∈ range 133, 4 * 4 := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          exact Nat.mul_le_mul (Nat.le_of_lt_succ (canon5_lane hx hj'))
            (Nat.le_of_lt_succ (canon5_lane (hY j hj') ht))
      _ < 2 ^ 16 := by norm_num
  rw [vm5_eq, lane5_red5 _ hk, e, lane_sum5 hb hk]

theorem idM_get {d i j : Nat} (hi : i < d) (hj : j < d) :
    ((idM d)[i]!)[j]! = if i = j then 1 else 0 := by
  unfold idM
  rw [ofFn_get! _ hi, ofFn_get! _ hj]

theorem colsMat_get {d i t : Nat} (vs : Array (Array Nat)) (hi : i < d) (ht : t < d) :
    ((colsMat d vs)[i]!)[t]! = (vs[t]!)[i]! := by
  unfold colsMat
  rw [ofFn_get! _ hi, ofFn_get! _ ht]

theorem col_get {d k j : Nat} (Y : Array (Array Nat)) (hj : j < d) :
    (col d Y k)[j]! = (Y[j]!)[k]! := by
  unfold col
  rw [ofFn_get! _ hj]

theorem all_ofFn_lt {n p : Nat} {f : Fin n → Nat} (h : ∀ j, f j < p) :
    (Array.ofFn f).all (· < p) = true := by
  rw [Array.all_eq_true]
  intro j hj
  rw [Array.getElem_ofFn]
  exact decide_eq_true (h _)

theorem digRun5_spec {x : Nat} : ∀ (cs : List Char) (j : Nat), digRun5 x cs j = true →
    cs.length + j = 133 ∧ ∀ t < cs.length, (cs.getD t '0').toNat - 48 = lane5 x (j + t)
  | [], j, h => by
    have e : digRun5 x [] j = Nat.beq j 133 := rfl
    rw [e] at h
    exact ⟨by simpa using Nat.eq_of_beq_eq_true h, fun t ht => absurd ht (by simp)⟩
  | ch :: cs, j, h => by
    have e : digRun5 x (ch :: cs) j = strictB ch.toNat (fun c => bAnd(Nat.ble 48 c,
        bAnd(Nat.beq (Nat.sub c 48) (lane5 x j), digRun5 x cs (Nat.succ j)))) := rfl
    rw [e, CFSG.KS.Raw.strictB_eq] at h
    obtain ⟨-, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨ih1, ih2⟩ := digRun5_spec cs (j + 1) h2
    refine ⟨by simp only [List.length_cons]; omega, fun t ht => ?_⟩
    cases t with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ t =>
      rw [List.getD_cons_succ, ih2 t (by simp only [List.length_cons] at ht; omega)]
      congr 1
      omega

theorem dig5K_spec {x : Nat} {cs : List Char} (h : dig5K x cs = true) :
    cs.length = 133 ∧ ∀ t < 133, (cs.getD t '0').toNat - 48 = lane5 x t := by
  unfold dig5K at h
  obtain ⟨hl, hd⟩ := digRun5_spec cs 0 ((CFSG.KS.bAnd_iff _ _).1 h).2
  refine ⟨by omega, fun t ht => ?_⟩
  rw [hd t (by omega), Nat.zero_add]

theorem ws5_eq (c : Char) : ws5 c.toNat = wsChar c := by
  have e : ws5 c.toNat = CFSG.KS.SporSch.wsK c.toNat := rfl
  rw [e, wsK_eq]

theorem ent5_eq (c : Nat) : ent5 c = digV c % 5 := by
  unfold ent5 digV
  cases Nat.ble 48 c <;> cases Nat.ble c 57 <;> rfl

theorem bIf_eq5 (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem pay5_cons0 (R : Nat → Nat) (ch : Char) (cs : List Char) (i j acc : Nat) :
    pay5Run R (ch :: cs) 0 i j acc =
      if ch.toNat = 10 then pay5Run R cs 1 i j acc else pay5Run R cs 0 i j acc := by
  have e : pay5Run R (ch :: cs) 0 i j acc = strictB ch.toNat (fun c =>
      bIf(Nat.beq c 10, pay5Run R cs 1 i j acc, pay5Run R cs 0 i j acc)) := rfl
  rw [e, CFSG.KS.Raw.strictB_eq, bIf_eq5]
  simp only [Nat.beq_eq]

theorem pay5_cons1 (R : Nat → Nat) (ch : Char) (cs : List Char) (i j acc : Nat) :
    pay5Run R (ch :: cs) 1 i j acc =
      if ws5 ch.toNat = true then pay5Run R cs 1 i j acc
      else if i < 133 then
        (if j + 1 = 133 then
          (if R i = Nat.lor acc (Nat.shiftLeft (ent5 ch.toNat) (Nat.mul (nat_lit 16) j)) then
            pay5Run R cs 1 (i + 1) 0 0 else false)
        else pay5Run R cs 1 i (j + 1) (Nat.lor acc (Nat.shiftLeft (ent5 ch.toNat)
          (Nat.mul (nat_lit 16) j))))
      else pay5Run R cs 1 i j acc := by
  have e : pay5Run R (ch :: cs) 1 i j acc = strictB ch.toNat (fun c =>
      bIf(ws5 c, pay5Run R cs 1 i j acc,
        bIf(Nat.blt i 133,
          strictB (Nat.lor acc (Nat.shiftLeft (ent5 c) (Nat.mul (nat_lit 16) j))) (fun acc' =>
            bIf(Nat.beq (Nat.succ j) 133,
              bAnd(Nat.beq (R i) acc', strictB (Nat.succ i) (fun i' => pay5Run R cs 1 i' 0 0)),
              strictB (Nat.succ j) (fun j' => pay5Run R cs 1 i j' acc'))),
          pay5Run R cs 1 i j acc))) := rfl
  rw [e]
  simp only [CFSG.KS.Raw.strictB_eq, bIf_eq5, Nat.blt_eq, Nat.beq_eq, Nat.succ_eq_add_one]

theorem pay5_ph0 (R : Nat → Nat) : ∀ (cs : List Char) (i j acc : Nat),
    pay5Run R cs 0 i j acc = pay5Run R ((cs.dropWhile (· != '\n')).drop 1) 1 i j acc := by
  intro cs
  induction cs with
  | nil => intro i j acc; rfl
  | cons ch cs ih =>
    intro i j acc
    rw [pay5_cons0]
    by_cases h : ch = '\n'
    · subst h
      have h10 : ('\n' : Char).toNat = 10 := rfl
      rw [ite_eq_left h10, List.dropWhile_cons_of_neg (by simp)]
      rfl
    · have h' : ch.toNat ≠ 10 := fun e => h (Char.toNat_inj.1 e)
      rw [ite_eq_right h', List.dropWhile_cons_of_pos (by simpa using h)]
      exact ih i j acc

theorem pay5_run1 {R : Nat → Nat} : ∀ (cs : List Char) (i j acc : Nat),
    pay5Run R cs 1 i j acc = true → i < 133 → j < 133 →
    (∀ c, j ≤ c → c < 133 → lane5 acc c = 0) →
    ∀ r, i ≤ r → r < 133 → ∀ c < 133, lane5 (R r) c =
      if r = i ∧ c < j then lane5 acc c else (esL cs).getD (133 * r + c - (133 * i + j)) 0 % 5 := by
  intro cs
  induction cs with
  | nil =>
    intro i j acc h hi hj hacc r hir hr c hc
    have e : pay5Run R [] 1 i j acc = bIf(Nat.blt i 133, bAnd(Nat.beq (R i) acc,
        allBlk (Nat.succ i) (fun r => Nat.beq (R r) 0) (Nat.sub 132 i)), true) := rfl
    have hb : Nat.blt i 133 = true := Eq.mpr Nat.blt_eq hi
    rw [e, hb] at h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    have hnil : ∀ n, (esL []).getD n 0 % 5 = 0 := fun n => by simp [esL]
    rw [hnil]
    rcases Nat.eq_or_lt_of_le hir with rfl | hlt
    · rw [Nat.eq_of_beq_eq_true h1]
      split_ifs with hc'
      · rfl
      · exact hacc c (by omega) hc
    · have h3 := CFSG.KS.allBlk_spec h2 (r - i - 1) (by change r - i - 1 < 132 - i; omega)
      change Nat.beq (R (i + 1 + (r - i - 1))) 0 = true at h3
      have e2 : i + 1 + (r - i - 1) = r := by omega
      rw [e2] at h3
      rw [Nat.eq_of_beq_eq_true h3, lane5_zero, ite_eq_right (by omega)]
  | cons ch cs ih =>
    intro i j acc h hi hj hacc r hir hr c hc
    rw [pay5_cons1] at h
    by_cases hw : ws5 ch.toNat = true
    · rw [ite_eq_left hw] at h
      have e : esL (ch :: cs) = esL cs := by
        unfold esL
        rw [List.filter_cons_of_neg (by rw [← ws5_eq, hw]; simp)]
      rw [e]
      exact ih i j acc h hi hj hacc r hir hr c hc
    · rw [ite_eq_right hw, ite_eq_left hi] at h
      have e : esL (ch :: cs) = digV ch.toNat :: esL cs := by
        unfold esL
        rw [List.filter_cons_of_pos (by rw [← ws5_eq]; simpa using hw), List.map_cons, digV_eq]
      rw [e]
      have hv5 : ent5 ch.toNat < 5 := by rw [ent5_eq]; exact Nat.mod_lt _ (by norm_num)
      have hv : ent5 ch.toNat < 2 ^ 16 := Nat.lt_trans hv5 (by norm_num)
      have hacc' : ∀ c', lane5 (Nat.lor acc (Nat.shiftLeft (ent5 ch.toNat)
          (Nat.mul (nat_lit 16) j))) c' =
          if c' = j then ent5 ch.toNat else lane5 acc c' := by
        intro c'
        rw [lane5_or_shl hv]
        split_ifs with h'
        · rw [h', hacc j le_rfl hj, Nat.zero_or]
        · rfl
      by_cases hj1 : j + 1 = 133
      · rw [ite_eq_left hj1] at h
        by_cases h1 : R i = Nat.lor acc (Nat.shiftLeft (ent5 ch.toNat) (Nat.mul (nat_lit 16) j))
        swap
        · rw [ite_eq_right h1] at h
          exact absurd h Bool.false_ne_true
        rw [ite_eq_left h1] at h
        have h2 := h
        rcases Nat.eq_or_lt_of_le hir with rfl | hlt
        · rw [h1, hacc' c]
          split_ifs with hcj hcj'
          · omega
          · subst hcj
            rw [Nat.sub_self, List.getD_cons_zero, ent5_eq]
          · rfl
          · omega
        · have := ih (i + 1) 0 0 h2 (by omega) (by omega) (fun c _ _ => lane5_zero c) r hlt hr c hc
          rw [this, ite_eq_right (by omega), ite_eq_right (by omega)]
          have e2 : 133 * r + c - (133 * i + j) = (133 * r + c - (133 * (i + 1) + 0)) + 1 := by
            omega
          rw [e2, List.getD_cons_succ]
      · rw [ite_eq_right hj1] at h
        have := ih i (j + 1) _ h hi (by omega) (fun c' h1 h2 => by
          rw [hacc' c', ite_eq_right (by omega)]
          exact hacc c' (by omega) h2) r hir hr c hc
        rw [this, hacc' c]
        by_cases hri : r = i
        · subst hri
          by_cases hcj : c < j
          · have c1 : r = r ∧ c < j + 1 := ⟨rfl, by omega⟩
            have c2 : r = r ∧ c < j := ⟨rfl, hcj⟩
            have c3 : c ≠ j := by omega
            rw [ite_eq_left c1, ite_eq_left c2, ite_eq_right c3]
          · by_cases hcj' : c = j
            · subst hcj'
              have c1 : r = r ∧ c < c + 1 := ⟨rfl, by omega⟩
              have c2 : ¬ (r = r ∧ c < c) := by omega
              rw [ite_eq_left c1, ite_eq_left rfl, ite_eq_right c2, Nat.sub_self,
                List.getD_cons_zero, ent5_eq]
            · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
              have e2 : 133 * r + c - (133 * r + j) = (133 * r + c - (133 * r + (j + 1))) + 1 := by
                omega
              rw [e2, List.getD_cons_succ]
        · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
          have e2 : 133 * r + c - (133 * i + j) = (133 * r + c - (133 * i + (j + 1))) + 1 := by
            omega
          rw [e2, List.getD_cons_succ]

theorem pay5_rows {R : Nat → Nat} {cs : List Char} (h : pay5K R cs = true) :
    rowsOf 5 133 (String.ofList cs) =
      Array.ofFn (n := 133) fun i => Array.ofFn (n := 133) fun j => lane5 (R i.val) j.val := by
  unfold pay5K at h
  rw [pay5_ph0] at h
  have hrun := pay5_run1 _ 0 0 0 h (by norm_num) (by norm_num) (fun c _ _ => lane5_zero c)
  have hdec : decodeEntries (String.ofList cs) = esL ((cs.dropWhile (· != '\n')).drop 1) := by
    unfold decodeEntries
    rw [String.toList_ofList]
    rfl
  unfold rowsOf
  rw [hdec]
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  have h := hrun i.val (Nat.zero_le _) i.isLt j.val j.isLt
  rw [ite_eq_right (by omega), Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at h
  rw [h, List.getElem?_toArray, List.getD_eq_getElem?_getD, Nat.mul_comm i.val 133]

end CFSG.KS.SporSch.F5Lane

end
