module

public import Certificates.Data.Kernel.E6TT.Enum
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTRoots

public section

namespace CFSG.KC.E6TT

open CFSG.KC.Enum (strictN strictB)
open Certificates.Data.E6TableT (Vec dot iform reps cartan)

theorem strictN_eqE (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eqE (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem nIf_eqE (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem bIf_true {c t : Bool} (h : Bool.rec (motive := fun _ => Bool) true t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem beq_zero_eqE (x : Nat) : Nat.beq x 0 = decide (x = 0) := by
  cases x <;> rfl

theorem lor_shiftLeft_eqE {a s : Nat} (ha : a < 2 ^ s) (b : Nat) :
    Nat.lor a (Nat.shiftLeft b s) = 2 ^ s * b + a := by
  change a ||| b <<< s = _
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.mul_comm]

theorem allBelow_specE {m hi : Nat} {f : Nat → Bool} (h : CFSG.KC.Loop.allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  have inner : ∀ (hh : Nat) (n : Nat), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft hh 6) l < m → f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro hh n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl hlm
      obtain ⟨h1, h2⟩ := bAnd_true hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact ih h2 l hl hlm
      · exact bIf_true h1 (Nat.blt_eq.mpr hlm)
  have outer : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun hh ih => bAnd(
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) 64,
        ih)) n = true → ∀ hh < n, ∀ l < 64, Nat.add (Nat.shiftLeft hh 6) l < m →
          f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro n
    induction n with
    | zero => intro _ hh hhh; omega
    | succ n ih =>
      intro hn hh hhh l hl hlm
      obtain ⟨h1, h2⟩ := bAnd_true hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhh with hhh | rfl
      · exact ih h2 hh hhh l hl hlm
      · exact inner _ 64 h1 l hl hlm
  intro i him hih
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have := outer hi h (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by norm_num)) (by rw [e]; exact him)
  rwa [e] at this

@[expose] def packL : List Nat → Nat
  | [] => 0
  | e :: es => 2 ^ 7 * packL es + (e + 1)

theorem sumP_succ (m : Nat) (f : Nat → Nat) (p : Nat) :
    sumP (m + 1) f p = if p % 128 = 0 then 0 else f (p % 128 - 1) + sumP m f (p / 128) := by
  simp only [sumP, strictN_eqE, nIf_eqE]
  have h1 : Nat.land p 127 = p % 128 := Nat.and_two_pow_sub_one_eq_mod p 7
  have h2 : Nat.shiftRight p 7 = p / 128 := Nat.shiftRight_eq_div_pow p 7
  rw [h1, h2]
  simp only [beq_zero_eqE, decide_eq_true_eq]
  by_cases h : p % 128 = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rfl

theorem le_sumP (f : Nat → Nat) : ∀ (l : List Nat) (m : Nat), l.length ≤ m →
    (∀ e ∈ l, e < 127) → ∀ a ∈ l, f a ≤ sumP m f (packL l)
  | [], _, _, _, a, ha => absurd ha (List.not_mem_nil)
  | e :: es, 0, hl, _, _, _ => by simp at hl
  | e :: es, m + 1, hl, he, a, ha => by
    have he0 : e < 127 := he e (by simp)
    have hmod : packL (e :: es) % 128 = e + 1 := by
      simp only [packL]; omega
    have hdiv : packL (e :: es) / 128 = packL es := by
      simp only [packL]; omega
    rw [sumP_succ, if_neg (by omega), hmod, hdiv, Nat.add_sub_cancel]
    rcases List.mem_cons.1 ha with rfl | ha
    · exact Nat.le_add_right _ _
    · exact le_trans (le_sumP f es m (by simp at hl; omega)
        (fun x hx => he x (List.mem_cons_of_mem _ hx)) a ha) (Nat.le_add_left _ _)

theorem length_le_of_packL_lt : ∀ (l : List Nat) (m : Nat), packL l < 128 ^ m → l.length ≤ m
  | [], _, _ => Nat.zero_le _
  | e :: es, 0, h => by simp only [packL, pow_zero] at h; omega
  | e :: es, m + 1, h => by
    simp only [packL, List.length_cons] at h ⊢
    have : packL es < 128 ^ m := by rw [pow_succ] at h; omega
    have := length_le_of_packL_lt es m this
    omega

theorem packF_aux (n : Nat) (pr : Nat → Bool) (hn : n ≤ 127) : ∀ j ≤ n,
    (Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => if pr ((n.sub j).sub 1) = true then
        (acc.shiftLeft 7).lor ((n.sub j).sub 1).succ else acc) j : Nat) =
      packL ((List.range' (n - j) j).filter pr)
  | 0, _ => rfl
  | j + 1, hj => by
    dsimp only
    rw [packF_aux n pr hn j (by omega)]
    have hr : List.range' (n - (j + 1)) (j + 1) = (n - j - 1) :: List.range' (n - j) j := by
      have e1 : n - (j + 1) + 1 = n - j := by omega
      have e2 : n - (j + 1) = n - j - 1 := by omega
      rw [List.range'_succ, e1, e2]
    change _ = packL ((List.range' (n - (j + 1)) (j + 1)).filter pr)
    rw [hr, List.filter_cons]
    change (if pr (n - j - 1) = true then ((packL _) <<< 7) ||| (n - j - 1 + 1) else packL _) =
      packL (if pr (n - j - 1) = true then _ else _)
    by_cases hp : pr (n - j - 1) = true
    · rw [if_pos hp, if_pos hp, packL]
      rw [← Nat.shiftLeft_add_eq_or_of_lt
        (lt_of_lt_of_le (by omega : n - j - 1 + 1 < 128) (by norm_num)), Nat.shiftLeft_eq,
        Nat.mul_comm]
    · rw [if_neg hp, if_neg hp]

theorem packF_eq (n : Nat) (pr : Nat → Bool) (hn : n ≤ 127) :
    packF n pr = packL ((List.range n).filter pr) := by
  have e : packF n pr = (Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => if pr ((n.sub j).sub 1) = true then
        (acc.shiftLeft 7).lor ((n.sub j).sub 1).succ else acc) n : Nat) := by
    simp only [packF, strictN_eqE, nIf_eqE]
  rw [e]
  have := packF_aux n pr hn n le_rfl
  rw [Nat.sub_self, ← List.range_eq_range'] at this
  exact this

theorem le_sumP_packF (f : Nat → Nat) {n m : Nat} {pr : Nat → Bool} (hn : n ≤ 127)
    (hm : packF n pr < 128 ^ m) {a : Nat} (ha : a < n) (hpa : pr a = true) :
    f a ≤ sumP m f (packF n pr) := by
  rw [packF_eq n pr hn] at hm ⊢
  refine le_sumP f _ m (length_le_of_packL_lt _ m hm) ?_ a ?_
  · intro e he
    have := (List.mem_range.1 (List.mem_filter.1 he).1)
    omega
  · exact List.mem_filter.2 ⟨List.mem_range.2 ha, hpa⟩

theorem le_sumP_packF_len (f : Nat → Nat) {n m : Nat} {pr : Nat → Bool} (hn : n ≤ 127)
    (hnm : n ≤ m) {a : Nat} (ha : a < n) (hpa : pr a = true) :
    f a ≤ sumP m f (packF n pr) := by
  rw [packF_eq n pr hn]
  refine le_sumP f _ m (le_trans (List.length_filter_le _ _) (by simpa using hnm)) ?_ a ?_
  · intro e he
    have := (List.mem_range.1 (List.mem_filter.1 he).1)
    omega
  · exact List.mem_filter.2 ⟨List.mem_range.2 ha, hpa⟩

theorem slotOf_lt (N i : Nat) : slotOf N i < 128 ^ 20 := by
  have hm : (1393796574908163946345982392040522594123775 : Nat) < 2 ^ 140 := by norm_num
  have h := Nat.and_lt_two_pow (N >>> (140 * i)) hm
  have e : (2 : Nat) ^ 140 = 128 ^ 20 := by norm_num
  rw [e] at h
  exact h

theorem le_sumP_slot (f : Nat → Nat) {N i : Nat} {pr : Nat → Bool}
    (hN : slotOf N i = packF 72 pr) {a : Nat} (ha : a < 72) (hpa : pr a = true) :
    f a ≤ sumP 20 f (slotOf N i) := by
  have hlt := slotOf_lt N i
  rw [hN] at hlt ⊢
  exact le_sumP_packF f (by norm_num) hlt ha hpa

theorem lane_eqE (r j : Nat) : lane r j = r / 8 ^ j % 8 := by
  change (r >>> (3 * j)) &&& (2 ^ 3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem rowCalc_cons (x y : Vec) (ys : List Vec) :
    rowCalc x (y :: ys) = 8 * rowCalc x ys + Int.toNat (iform x y % 8) := by
  change Nat.lor (Int.toNat (iform x y % 8)) (Nat.shiftLeft (rowCalc x ys) 3) = _
  have h1 := Int.emod_lt_of_pos (iform x y) (by norm_num : (0 : Int) < 8)
  have h2 := Int.emod_nonneg (iform x y) (by norm_num : (8 : Int) ≠ 0)
  have h3 : Int.toNat (iform x y % 8) < 2 ^ 3 := by
    have : Int.toNat (iform x y % 8) < 8 := by omega
    simpa using this
  rw [lor_shiftLeft_eqE h3]
  rfl

theorem lane_rowCalc (x : Vec) : ∀ (R : List Vec) (j : Nat), j < R.length →
    lane (rowCalc x R) j = Int.toNat (iform x (R.getD j []) % 8)
  | [], j, h => absurd h (Nat.not_lt_zero _)
  | y :: ys, 0, _ => by
    have h1 := Int.emod_lt_of_pos (iform x y) (by norm_num : (0 : Int) < 8)
    have h2 := Int.emod_nonneg (iform x y) (by norm_num : (8 : Int) ≠ 0)
    rw [lane_eqE, rowCalc_cons]
    simp only [pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | y :: ys, j + 1, h => by
    have h1 := Int.emod_lt_of_pos (iform x y) (by norm_num : (0 : Int) < 8)
    have h2 := Int.emod_nonneg (iform x y) (by norm_num : (8 : Int) ≠ 0)
    have e8 : (8 : Nat) ^ (j + 1) = 8 * 8 ^ j := pow_succ' 8 j
    rw [lane_eqE, rowCalc_cons, e8, ← Nat.div_div_eq_div_mul]
    have e : (8 * rowCalc x ys + Int.toNat (iform x y % 8)) / 8 = rowCalc x ys := by
      omega
    rw [e, ← lane_eqE, lane_rowCalc x ys j (by simp at h; omega), List.getD_cons_succ]

theorem bits_spec (g : Nat → Bool) : ∀ ls : List Nat,
    (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun l _ ih => Nat.lor (bif g l then nat_lit 1 else nat_lit 0) (Nat.shiftLeft ih (nat_lit 1)))
      ls : Nat) < 2 ^ ls.length ∧
    ∀ i < ls.length, (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun l _ ih => Nat.lor (bif g l then nat_lit 1 else nat_lit 0) (Nat.shiftLeft ih (nat_lit 1)))
      ls : Nat).testBit i = g (ls.getD i 0)
  | [] => ⟨by simp, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | l :: ls => by
    obtain ⟨hlt, hbit⟩ := bits_spec g ls
    have hb : (bif g l then 1 else 0 : Nat) < 2 ^ 1 := by cases g l <;> decide
    change Nat.lor (bif g l then 1 else 0) (Nat.shiftLeft _ 1) < _ ∧
      ∀ i < (l :: ls).length, (Nat.lor (bif g l then 1 else 0) (Nat.shiftLeft _ 1)).testBit i = _
    rw [lor_shiftLeft_eqE hb]
    refine ⟨?_, ?_⟩
    · simp only [List.length_cons, pow_succ] at hlt ⊢
      omega
    · intro i hi
      rw [Nat.testBit_two_pow_mul_add _ hb]
      rcases i with _ | i
      · rw [if_pos (by omega), List.getD_cons_zero]
        cases g l <;> rfl
      · rw [if_neg (by omega), Nat.add_sub_cancel, List.getD_cons_succ]
        exact hbit i (by simp at hi; omega)

theorem repFlags_spec (x v : Vec) :
    repFlags x v < 2 ^ 6 ∧ ∀ l < 6, (repFlags x v).testBit l = resFlag x v l := by
  obtain ⟨h1, h2⟩ := bits_spec (resFlag x v) [0, 1, 2, 3, 4, 5]
  refine ⟨h1, fun l hl => ?_⟩
  have := h2 l hl
  interval_cases l <;> exact this

theorem flags_spec (x : Vec) : ∀ (L : List Vec) (k l : Nat), k < L.length → l < 6 →
    (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun v _ ih => Nat.lor (repFlags x v) (Nat.shiftLeft ih (nat_lit 6))) L : Nat).testBit
        (6 * k + l) = resFlag x (L.getD k []) l
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | v :: vs, k, l, hk, hl => by
    obtain ⟨hlt, hbit⟩ := repFlags_spec x v
    change (Nat.lor (repFlags x v) (Nat.shiftLeft _ 6)).testBit _ = _
    rw [lor_shiftLeft_eqE hlt, Nat.testBit_two_pow_mul_add _ hlt]
    rcases k with _ | k
    · rw [if_pos (by omega), List.getD_cons_zero, Nat.mul_zero, Nat.zero_add]
      exact hbit l hl
    · rw [if_neg (by omega), List.getD_cons_succ]
      have e : 6 * (k + 1) + l - 6 = 6 * k + l := by omega
      rw [e]
      exact flags_spec x vs k l (by simp at hk; omega) hl

theorem flagsCalc_testBit (x : Vec) {k l : Nat} (hk : k < 5) (hl : l < 6) :
    (flagsCalc x).testBit (6 * k + l) = resFlag x (reps.getD k []) l :=
  flags_spec x reps k l hk hl

theorem bitF_eqE (FL j b : Nat) : bitF FL j b = (flOf FL j).testBit b := by
  change Nat.beq ((flOf FL j >>> b) &&& 1) 1 = _
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (flOf FL j / 2 ^ b) with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

theorem land_shiftLeft_eqE (r c s : Nat) : r &&& (c <<< s) = ((r >>> s) &&& c) <<< s := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s ≤ i
  · simp [h, Nat.add_sub_cancel' h]
  · simp [h]

theorem zt_lm {r a : Nat} (h : lane r a = 0) : zt r (lm a) = true := by
  change Nat.beq (r &&& (7 <<< (3 * a))) 0 = true
  rw [land_shiftLeft_eqE]
  change Nat.beq ((lane r a) <<< (3 * a)) 0 = true
  rw [h, Nat.zero_shiftLeft]
  rfl

theorem zt_lor (r m1 m2 : Nat) : zt r (Nat.lor m1 m2) = (zt r m1 && zt r m2) := by
  change Nat.beq (r &&& (m1 ||| m2)) 0 = (Nat.beq (r &&& m1) 0 && Nat.beq (r &&& m2) 0)
  rw [Nat.and_or_distrib_left]
  simp only [beq_zero_eqE, Nat.or_eq_zero_iff, Bool.decide_and]

theorem allIdx_spec (f : Nat → Vec → Bool) : ∀ (R : List Vec) (i : Nat), allIdx f R i = true →
    ∀ j < R.length, f (i + j) (R.getD j []) = true
  | [], _, _, j, h => absurd h (Nat.not_lt_zero _)
  | x :: xs, i, h, j, hj => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    rcases j with _ | j
    · exact h1
    · have := allIdx_spec f xs (i + 1) h2 j (by simp at hj; omega)
      rw [List.getD_cons_succ]
      rwa [show i + 1 + j = i + (j + 1) by omega] at this

theorem grOK_spec {R : List Vec} {GR FL : Nat} (h : grOK R GR FL = true) :
    R.length = 72 ∧ ∀ i < 72, rowOf GR i = rowCalc (R.getD i []) R ∧
      flOf FL i = flagsCalc (R.getD i []) := by
  obtain ⟨h1, h2⟩ := bAnd_true h
  have hl : R.length = 72 := Nat.eq_of_beq_eq_true h1
  refine ⟨hl, fun i hi => ?_⟩
  have := allIdx_spec _ R 0 h2 i (by omega)
  rw [Nat.zero_add] at this
  obtain ⟨h3, h4⟩ := bAnd_true this
  exact ⟨Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem lvlOK_spec {GR FL b N : Nat} (h : lvlOK GR FL b N = true) : ∀ i < 72,
    slotOf N i = packF 72 (fun j => Nat.beq (lane (rowOf GR i) j) 7 && bitF FL j b) := by
  intro i hi
  have := allBelow_specE h i hi (by norm_num; omega)
  rw [strictB_eqE] at this
  exact Nat.eq_of_beq_eq_true this

theorem nbOK_spec {GR FL k L0 N1 N2 N3 N4 N5 : Nat} (h : nbOK GR FL k L0 N1 N2 N3 N4 N5 = true) :
    L0 = packF 72 (fun j => bitF FL j (6 * k)) ∧ lvlOK GR FL (6 * k + 1) N1 = true ∧
      lvlOK GR FL (6 * k + 2) N2 = true ∧ lvlOK GR FL (6 * k + 3) N3 = true ∧
      lvlOK GR FL (6 * k + 4) N4 = true ∧ lvlOK GR FL (6 * k + 5) N5 = true := by
  change strictB (6 * k) (fun b => bAnd(Nat.beq L0 (packF 72 fun j => bitF FL j b),
    bAnd(lvlOK GR FL (b + 1) N1, bAnd(lvlOK GR FL (b + 2) N2, bAnd(lvlOK GR FL (b + 3) N3,
    bAnd(lvlOK GR FL (b + 4) N4, lvlOK GR FL (b + 5) N5)))))) = true at h
  rw [strictB_eqE] at h
  obtain ⟨h0, h⟩ := bAnd_true h
  obtain ⟨h1, h⟩ := bAnd_true h
  obtain ⟨h2, h⟩ := bAnd_true h
  obtain ⟨h3, h⟩ := bAnd_true h
  obtain ⟨h4, h5⟩ := bAnd_true h
  exact ⟨Nat.eq_of_beq_eq_true h0, h1, h2, h3, h4, h5⟩

theorem le_enumK {R : List Vec} {GR FL k L0 N1 N2 N3 N4 N5 : Nat} (hk : k < 5)
    (hg : grOK R GR FL = true) (hn : nbOK GR FL k L0 N1 N2 N3 N4 N5 = true)
    (leaf : Nat → Nat → Nat → Nat → Nat → Nat → Nat) (a : Fin 6 → Nat) (ha : ∀ i, a i < 72)
    (hgram : ∀ i j : Fin 6,
      iform (R.getD (a i) []) (R.getD (a j) []) = (cartan.getD i []).getD j 0)
    (hres : ∀ i : Fin 6, resFlag (R.getD (a i) []) (reps.getD k []) i = true) :
    leaf (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) ≤ enumK GR L0 N1 N2 N3 N4 N5 leaf := by
  obtain ⟨hlen, hrow⟩ := grOK_spec hg
  have hlane : ∀ i j : Fin 6, lane (rowOf GR (a i)) (a j) =
      Int.toNat (iform (R.getD (a i) []) (R.getD (a j) []) % 8) := fun i j => by
    rw [(hrow (a i) (ha i)).1]
    exact lane_rowCalc _ R (a j) (by rw [hlen]; exact ha j)
  have hnb : ∀ i j : Fin 6, (cartan.getD i []).getD j 0 = -1 →
      Nat.beq (lane (rowOf GR (a i)) (a j)) 7 = true := fun i j h => by
    rw [hlane, hgram, h]
    rfl
  have hor : ∀ i j : Fin 6, (cartan.getD i []).getD j 0 = 0 → lane (rowOf GR (a i)) (a j) = 0 :=
    fun i j h => by
      rw [hlane, hgram, h]
      rfl
  have hfl : ∀ i : Fin 6, bitF FL (a i) (6 * k + i) = true := fun i => by
    rw [bitF_eqE, (hrow (a i) (ha i)).2, flagsCalc_testBit _ hk i.2]
    exact hres i
  obtain ⟨hL0, h1, h2, h3, h4, h5⟩ := nbOK_spec hn
  have s1 := lvlOK_spec h1
  have s2 := lvlOK_spec h2
  have s3 := lvlOK_spec h3
  have s4 := lvlOK_spec h4
  have s5 := lvlOK_spec h5
  have f0 : bitF FL (a 0) (6 * k) = true := hfl 0
  have f1 : bitF FL (a 1) (6 * k + 1) = true := hfl 1
  have f2 : bitF FL (a 2) (6 * k + 2) = true := hfl 2
  have f3 : bitF FL (a 3) (6 * k + 3) = true := hfl 3
  have f4 : bitF FL (a 4) (6 * k + 4) = true := hfl 4
  have f5 : bitF FL (a 5) (6 * k + 5) = true := hfl 5
  simp only [enumK, strictN_eqE, nIf_eqE]
  rw [hL0]
  refine le_trans ?_ (le_sumP_packF_len _ (by norm_num) le_rfl (ha 0) f0)
  refine le_trans ?_ (le_sumP_slot _ (s2 (a 0) (ha 0)) (ha 2)
    (by rw [hnb 0 2 (by decide), f2]; rfl))
  refine le_trans ?_ (le_sumP_slot _ (s3 (a 2) (ha 2)) (ha 3)
    (by rw [hnb 2 3 (by decide), f3]; rfl))
  rw [if_pos (zt_lm (hor 3 0 (by decide)))]
  refine le_trans ?_ (le_sumP_slot _ (s1 (a 3) (ha 3)) (ha 1)
    (by rw [hnb 3 1 (by decide), f1]; rfl))
  rw [if_pos (by rw [zt_lor, zt_lm (hor 1 0 (by decide)), zt_lm (hor 1 2 (by decide))]; rfl)]
  refine le_trans ?_ (le_sumP_slot _ (s4 (a 3) (ha 3)) (ha 4)
    (by rw [hnb 3 4 (by decide), f4]; rfl))
  rw [if_pos (by rw [zt_lor, zt_lor, zt_lm (hor 4 0 (by decide)), zt_lm (hor 4 2 (by decide)),
    zt_lm (hor 4 1 (by decide))]; rfl)]
  refine le_trans ?_ (le_sumP_slot _ (s5 (a 4) (ha 4)) (ha 5)
    (by rw [hnb 4 5 (by decide), f5]; rfl))
  rw [if_pos (by rw [zt_lor, zt_lor, zt_lor, zt_lm (hor 5 0 (by decide)),
    zt_lm (hor 5 2 (by decide)), zt_lm (hor 5 1 (by decide)), zt_lm (hor 5 3 (by decide))]; rfl)]

section Bridge

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
open CFSG.StandardType.TablePThreeKG (E6Admissible repZ vecZ)
open Certificates.Data.E6TableT (roots)

theorem dot_cons_consE (a b : ℤ) (as bs : Vec) : dot (a :: as) (b :: bs) = a * b + dot as bs := by
  simp only [dot, List.zipWith_cons_cons, List.sum_cons]

theorem dot_ofFnE : ∀ (n : ℕ) (x : Fin n → ℤ) (l : Vec),
    dot (List.ofFn x) l = ∑ i : Fin n, x i * l.getD i 0
  | 0, x, l => by simp [dot]
  | n + 1, x, l => by
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    cases l with
    | nil => simp [dot]
    | cons b bs =>
      rw [dot_cons_consE, dot_ofFnE n (fun i => x i.succ) bs]
      simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]

theorem cartan_getD_mapE (f : Vec → ℤ) {n : ℕ} (hn : n < 6) :
    (cartan.map f).getD n 0 = f (cartan.getD n []) := by
  have hl : cartan.length = 6 := rfl
  rw [List.getD_eq_getElem _ _ (by simpa [List.length_map, hl] using hn),
    List.getElem_map, List.getD_eq_getElem _ _ (by simpa [hl] using hn)]

theorem cartan_entryE (i j : Fin Tag.E6.rank) :
    (cartan.getD i.val []).getD j.val 0 = Tag.E6.symmetrizedCartan i j := by
  have e : Tag.E6.symmetrizedCartan i j = Tag.E6.cartan i j := by
    simp [Tag.symmetrizedCartan, Tag.symmetrizer]
  rw [e]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem advIform_singleE (k j : Fin Tag.E6.rank) :
    CFSG.LieType.Steinberg.Adjoint.iform (Pi.single k 1) (Pi.single j 1) =
      (cartan.getD k.val []).getD j.val 0 := by
  rw [CFSG.LieType.Steinberg.Adjoint.iform]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same, one_mul, mul_one]
      exact (cartan_entryE k j).symm
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem checker_iform_ofFnE (x y : Fin Tag.E6.rank → ℤ) :
    iform (List.ofFn x) (List.ofFn y) = CFSG.LieType.Steinberg.Adjoint.iform x y := by
  rw [iform, CFSG.LieType.Steinberg.Adjoint.iform, dot_ofFnE]
  apply Finset.sum_congr rfl
  intro i _
  rw [cartan_getD_mapE (dot (List.ofFn y)) i.2, dot_ofFnE, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [cartan_entryE i j]
  ring

theorem e6Admissible_le_enumK {GR FL L0 N1 N2 N3 N4 N5 : Nat} (k : Fin 5)
    (hg : grOK (roots ()) GR FL = true) (hn : nbOK GR FL k L0 N1 N2 N3 N4 N5 = true)
    (leaf : Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (b : Fin Tag.E6.rank → (Fin Tag.E6.rank → ℤ)) (h : E6Admissible b (repZ k) 2) :
    ∃ a : Fin 6 → Nat, (∀ i, a i < 72 ∧ (roots ()).getD (a i) [] = List.ofFn (b i)) ∧
      leaf (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) ≤ enumK GR L0 N1 N2 N3 N4 N5 leaf := by
  have hlen := (grOK_spec hg).1
  have hex : ∀ i : Fin 6, ∃ n, n < 72 ∧ (roots ()).getD n [] = List.ofFn (b i) := fun i => by
    have hm := (CFSG.StandardType.TablePThreeKG.isRoot_iff_mem_roots (b i)).mp (h.1 i)
    obtain ⟨n, hn', he⟩ := List.mem_iff_getElem.1 hm
    exact ⟨n, hlen ▸ hn', by rw [List.getD_eq_getElem _ _ hn', he]⟩
  choose a ha using hex
  refine ⟨a, ha, le_enumK k.2 hg hn leaf a (fun i => (ha i).1) ?_ ?_⟩
  · intro i j
    rw [(ha i).2, (ha j).2, checker_iform_ofFnE, h.2.1 i j]
    exact advIform_singleE i j
  · intro i
    rw [(ha i).2]
    unfold resFlag
    rw [beq_iff_eq]
    apply Int.emod_eq_zero_of_dvd
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    have hrep : ∀ m : Fin Tag.E6.rank,
        (repZ k) m = (((reps.getD k []).getD m.val 0 : ℤ) : ZMod 3) := fun m => by
      simp [repZ, vecZ]
    have hdot : (dot (List.ofFn (b i)) (reps.getD k []) : ZMod 3) =
        ∑ m : Fin Tag.E6.rank, ((b i m : ℤ) : ZMod 3) * (repZ k) m := by
      rw [dot_ofFnE]
      push_cast
      apply Finset.sum_congr rfl
      intro m _
      rw [hrep m]
    have hsum := h.2.2 i
    rw [Int.cast_sub, Int.cast_mul, hdot, hsum, hrep i]
    push_cast
    ring

end Bridge

end CFSG.KC.E6TT

end
