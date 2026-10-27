module

public import Certificates.Data.Kernel.CosetJ.F2Cert
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.KC.CosetJ.F2

@[expose] def ind (b : Bool) : ZMod 2 := if b then 1 else 0

theorem ind_xor (a b : Bool) : ind (a ^^ b) = ind a + ind b := by
  cases a <;> cases b <;> decide

theorem ind_and (a b : Bool) : ind (a && b) = ind a * ind b := by
  cases a <;> cases b <;> decide

theorem ind_decide (p : Prop) [Decidable p] : ind (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [ind, h]

theorem natXor_eq (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl

theorem natMul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl

theorem natShiftLeft_eq (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl

theorem natAdd_eq (a b : ℕ) : Nat.add a b = a + b := rfl

theorem ind_testBit_xorN (n : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    ind ((xorN n f).testBit k) = ∑ q ∈ Finset.range n, ind ((f q).testBit k) := by
  induction n with
  | zero => simp [xorN, ind]
  | succ n ih =>
    have e : xorN (n + 1) f = f n ^^^ xorN n f := rfl
    rw [e, Nat.testBit_xor, ind_xor, ih, Finset.sum_range_succ, add_comm]

theorem bit_eq (x i : ℕ) : bit x i = if x.testBit i then 1 else 0 := by
  have h1 : bit x i = x / 2 ^ i % 2 := by
    show Nat.land (x >>> i) 1 = _
    rw [show Nat.land (x >>> i) 1 = (x >>> i) &&& 1 from rfl, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow]
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

theorem mulBit_eq (x i y : ℕ) : bit x i * y = if x.testBit i then y else 0 := by
  rw [bit_eq]
  split_ifs <;> simp

theorem testBit_mulBit (x i y k : ℕ) :
    (bit x i * y).testBit k = (x.testBit i && y.testBit k) := by
  rw [mulBit_eq]
  split_ifs with h <;> simp [h]

theorem testBit_shiftLeft_field {R w r r' c : ℕ} (hc : c < w) (hR : R < 2 ^ w) :
    (R <<< (w * r)).testBit (w * r' + c) = (decide (r = r') && R.testBit c) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : r = r'
  · subst h
    simp
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · have hle : w * (r + 1) ≤ w * r' := Nat.mul_le_mul_left w h'
      have hge : w ≤ w * r' + c - w * r := by rw [Nat.mul_succ] at hle; omega
      have hb : R.testBit (w * r' + c - w * r) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hR (Nat.pow_le_pow_right Nat.two_pos hge))
      rw [hb, Bool.and_false, decide_eq_false h, Bool.false_and]
    · have hle : w * (r' + 1) ≤ w * r := Nat.mul_le_mul_left w h'
      have hlt : ¬ (w * r' + c ≥ w * r) := by rw [Nat.mul_succ] at hle; omega
      rw [decide_eq_false hlt, Bool.false_and, decide_eq_false h, Bool.false_and]

@[expose] noncomputable def spreadGo (q R w : ℕ) (S : List ℕ) (s : ℕ) : ℕ :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih r => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ r))
      (Nat.xor (Nat.mul (bit x q) (Nat.shiftLeft R (Nat.mul w r))) (ih (Nat.succ r)))
      (Nat.blt r 121))
    S s

theorem spread_eq (S : List ℕ) (q R w : ℕ) : spread S q R w = spreadGo q R w S 0 := rfl

theorem testBit_spreadGo {q R w c : ℕ} (hc : c < w) (hR : R < 2 ^ w) (r : ℕ) :
    ∀ (S : List ℕ) (s : ℕ), (spreadGo q R w S s).testBit (w * r + c) =
      (decide (s ≤ r ∧ r < 121) && ((S.getD (r - s) 0).testBit q && R.testBit c))
  | [], s => by
    simp only [spreadGo, Nat.zero_testBit, List.getD_nil, Bool.and_false, Bool.false_and]
  | x :: S, s => by
    have e : spreadGo q R w (x :: S) s = Bool.rec (motive := fun _ => Nat) (spreadGo q R w S (s + 1))
        (Nat.xor (Nat.mul (bit x q) (Nat.shiftLeft R (Nat.mul w s))) (spreadGo q R w S (s + 1)))
        (Nat.blt s 121) := rfl
    rw [e]
    have ih := testBit_spreadGo (q := q) hc hR r S (s + 1)
    by_cases hs : s < 121
    · have hb : Nat.blt s 121 = true := by rw [Nat.blt_eq]; exact hs
      rw [hb]
      show (bit x q * (R <<< (w * s)) ^^^ spreadGo q R w S (s + 1)).testBit (w * r + c) = _
      rw [Nat.testBit_xor, testBit_mulBit, testBit_shiftLeft_field hc hR, ih]
      by_cases hrs : r = s
      · subst hrs
        simp [hs]
      · by_cases hsr : s + 1 ≤ r
        · have h3 : r - s = (r - (s + 1)) + 1 := by omega
          simp [Ne.symm hrs, hrs, hsr, h3, show s ≤ r by omega]
        · have h4 : ¬ (s ≤ r ∧ r < 121) := by omega
          simp [Ne.symm hrs, hsr, h4]
    · have hb : Nat.blt s 121 = false := by
        rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
        exact hs
      rw [hb]
      show (spreadGo q R w S (s + 1)).testBit (w * r + c) = _
      rw [ih]
      by_cases hr : r < 121
      · have h5 : ¬ (s + 1 ≤ r ∧ r < 121) := by omega
        have h6 : ¬ (s ≤ r ∧ r < 121) := by omega
        rw [decide_eq_false h5, decide_eq_false h6, Bool.false_and, Bool.false_and]
      · simp [hr]

theorem testBit_spread {S : List ℕ} {q R w c r : ℕ} (hc : c < w) (hR : R < 2 ^ w) (hr : r < 121) :
    (spread S q R w).testBit (w * r + c) = ((S.getD r 0).testBit q && R.testBit c) := by
  rw [spread_eq, testBit_spreadGo hc hR r S 0]
  simp [hr]

@[expose] noncomputable def spreadYGo (q R : ℕ) (Y : List ℕ) (s : ℕ) : ℕ :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih r => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ r))
      (Nat.xor (Nat.mul (bit x q) (Nat.shiftLeft R (Nat.mul 22 r))) (ih (Nat.succ r)))
      (Nat.blt r 22))
    Y s

theorem spreadY_eq (Y : List ℕ) (q R : ℕ) : spreadY Y q R = spreadYGo q R Y 0 := rfl

theorem testBit_spreadYGo {q R c : ℕ} (hc : c < 22) (hR : R < 2 ^ 22) (r : ℕ) :
    ∀ (Y : List ℕ) (s : ℕ), (spreadYGo q R Y s).testBit (22 * r + c) =
      (decide (s ≤ r ∧ r < 22) && ((Y.getD (r - s) 0).testBit q && R.testBit c))
  | [], s => by
    simp only [spreadYGo, Nat.zero_testBit, List.getD_nil, Bool.and_false, Bool.false_and]
  | x :: Y, s => by
    have e : spreadYGo q R (x :: Y) s = Bool.rec (motive := fun _ => Nat) (spreadYGo q R Y (s + 1))
        (Nat.xor (Nat.mul (bit x q) (Nat.shiftLeft R (Nat.mul 22 s))) (spreadYGo q R Y (s + 1)))
        (Nat.blt s 22) := rfl
    rw [e]
    have ih := testBit_spreadYGo (q := q) hc hR r Y (s + 1)
    by_cases hs : s < 22
    · have hb : Nat.blt s 22 = true := by rw [Nat.blt_eq]; exact hs
      rw [hb]
      show (bit x q * (R <<< (22 * s)) ^^^ spreadYGo q R Y (s + 1)).testBit (22 * r + c) = _
      rw [Nat.testBit_xor, testBit_mulBit, testBit_shiftLeft_field hc hR, ih]
      by_cases hrs : r = s
      · subst hrs
        simp [hs]
      · by_cases hsr : s + 1 ≤ r
        · have h3 : r - s = (r - (s + 1)) + 1 := by omega
          simp [Ne.symm hrs, hrs, hsr, h3, show s ≤ r by omega]
        · have h4 : ¬ (s ≤ r ∧ r < 22) := by omega
          simp [Ne.symm hrs, hsr, h4]
    · have hb : Nat.blt s 22 = false := by
        rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
        exact hs
      rw [hb]
      show (spreadYGo q R Y (s + 1)).testBit (22 * r + c) = _
      rw [ih]
      by_cases hr : r < 22
      · have h5 : ¬ (s + 1 ≤ r ∧ r < 22) := by omega
        have h6 : ¬ (s ≤ r ∧ r < 22) := by omega
        rw [decide_eq_false h5, decide_eq_false h6, Bool.false_and, Bool.false_and]
      · simp [hr]

theorem testBit_spreadY {Y : List ℕ} {q R c r : ℕ} (hc : c < 22) (hR : R < 2 ^ 22) (hr : r < 22) :
    (spreadY Y q R).testBit (22 * r + c) = ((Y.getD r 0).testBit q && R.testBit c) := by
  rw [spreadY_eq, testBit_spreadYGo hc hR r Y 0]
  simp [hr]

theorem ind_testBit_idPack {n w r c : ℕ} (hc : c < w) (hr : r < n) (hn : n ≤ w) :
    ind ((idPack n w).testBit (w * r + c)) = if r = c then 1 else 0 := by
  rw [idPack, ind_testBit_xorN]
  have hterm : ∀ t ∈ Finset.range n, ind ((Nat.shiftLeft 1 (Nat.add (Nat.mul w t) t)).testBit
      (w * r + c)) = if t = r ∧ r = c then 1 else 0 := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [show Nat.shiftLeft 1 (Nat.add (Nat.mul w t) t) = 2 ^ (w * t + t) by
      rw [show Nat.shiftLeft 1 (Nat.add (Nat.mul w t) t) = 1 <<< (w * t + t) from rfl,
        Nat.one_shiftLeft], Nat.testBit_two_pow, ind_decide]
    congr 1
    apply propext
    constructor
    · intro h
      have h1 : t = r := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h' | h'
        · have : w * (t + 1) ≤ w * r := Nat.mul_le_mul_left w h'
          rw [Nat.mul_succ] at this
          omega
        · have : w * (r + 1) ≤ w * t := Nat.mul_le_mul_left w h'
          rw [Nat.mul_succ] at this
          omega
      subst h1
      exact ⟨rfl, by omega⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  rw [Finset.sum_congr rfl hterm]
  by_cases hrc : r = c
  · subst hrc
    simp [Finset.sum_ite_eq', Finset.mem_range, hr]
  · simp [hrc]

theorem sum_I2 (g : ℕ → ZMod 2) :
    ∑ q : Fin 11 × Fin 11, g (11 * q.1.val + q.2.val) = ∑ n ∈ Finset.range 121, g n := by
  have h1 : ∀ q : Fin 11 × Fin 11, 11 * q.1.val + q.2.val = (finProdFinEquiv q).val := by
    intro q
    show 11 * q.1.val + q.2.val = q.2.val + 11 * q.1.val
    omega
  simp only [h1]
  rw [Equiv.sum_comp finProdFinEquiv (fun k : Fin (11 * 11) => g k.val)]
  exact Fin.sum_univ_eq_sum_range g 121

theorem getL_eq : ∀ (L : List ℕ) (j : ℕ), getL L j = L.getD j 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, j + 1 => getL_eq L j

theorem testBit_col (a : List ℕ) (j i : ℕ) (hi : i < 11) :
    (col a j).testBit i = (a.getD j 0).testBit i := by
  show (getL a j &&& 2047).testBit i = _
  rw [Nat.testBit_and, getL_eq, show (2047 : ℕ) = 2 ^ 11 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp [hi]

theorem col_lt (a : List ℕ) (j : ℕ) : col a j < 2 ^ 11 := by
  show getL a j &&& 2047 < 2 ^ 11
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem e2_eq (i j : ℕ) : e2 i j = 2 ^ (11 * i + j) := by
  show 1 <<< (11 * i + j) = _
  exact Nat.one_shiftLeft _

theorem natDiv_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem natMod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem div_eleven {i j : ℕ} (hj : j < 11) : (11 * i + j) / 11 = i := by omega

theorem mod_eleven {i j : ℕ} (hj : j < 11) : (11 * i + j) % 11 = j := by omega

theorem idx_eq_iff {i j k l : ℕ} (hj : j < 11) (hl : l < 11) :
    11 * i + j = 11 * k + l ↔ i = k ∧ j = l := by omega

theorem xorN_lt (n m : ℕ) (f : ℕ → ℕ) (h : ∀ q < n, f q < 2 ^ m) : xorN n f < 2 ^ m := by
  induction n with
  | zero => exact Nat.two_pow_pos m
  | succ n ih =>
    show f n ^^^ xorN n f < 2 ^ m
    exact Nat.xor_lt_two_pow (h n (by omega)) (ih fun q hq => h q (by omega))

theorem e2_lt {i j : ℕ} (hi : i < 11) (hj : j < 11) : e2 i j < 2 ^ 121 := by
  rw [e2_eq]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem rowSym_lt {q : ℕ} (hq : q < 121) : rowSym q < 2 ^ 121 := by
  unfold rowSym
  simp only [natDiv_eq, natMod_eq, natXor_eq]
  exact Nat.xor_lt_two_pow (e2_lt (by omega) (Nat.mod_lt _ (by decide)))
    (e2_lt (Nat.mod_lt _ (by decide)) (by omega))

theorem rowDiag_lt {q : ℕ} (hq : q < 121) : rowDiag q < 2 ^ 121 := by
  unfold rowDiag
  simp only [natDiv_eq, natMod_eq]
  cases Nat.beq (q / 11) (q % 11)
  · exact Nat.two_pow_pos _
  · exact e2_lt (by omega) (Nat.mod_lt _ (by decide))

theorem rowInv_lt (a : List ℕ) {q : ℕ} (hq : q < 121) : rowInv a q < 2 ^ 121 := by
  unfold rowInv
  simp only [natDiv_eq, natMod_eq, natXor_eq, natMul_eq, natShiftLeft_eq]
  refine Nat.xor_lt_two_pow (xorN_lt _ _ _ fun u hu => ?_) (e2_lt (by omega) (Nat.mod_lt _ (by decide)))
  have hu' : u < 11 := hu
  rw [mulBit_eq]
  split_ifs
  · rw [Nat.shiftLeft_eq]
    calc col a (q % 11) * 2 ^ (11 * u) < 2 ^ 11 * 2 ^ (11 * u) :=
          Nat.mul_lt_mul_of_pos_right (col_lt a _) (Nat.two_pow_pos _)
      _ = 2 ^ (11 + 11 * u) := (Nat.pow_add 2 11 (11 * u)).symm
      _ ≤ 2 ^ 121 := Nat.pow_le_pow_right (by decide) (by omega)
  · exact Nat.two_pow_pos _

theorem ind_testBit_rowSym {i j k l : ℕ} (hi : i < 11) (hj : j < 11) (hk : k < 11) (hl : l < 11) :
    ind ((rowSym (11 * i + j)).testBit (11 * k + l)) =
      (if i = k ∧ j = l then 1 else 0) + (if j = k ∧ i = l then 1 else 0) := by
  unfold rowSym
  simp only [natDiv_eq, natMod_eq, natXor_eq]
  rw [div_eleven hj, mod_eleven hj, Nat.testBit_xor, ind_xor, e2_eq, e2_eq, Nat.testBit_two_pow,
    Nat.testBit_two_pow, ind_decide, ind_decide]
  simp only [idx_eq_iff hj hl, idx_eq_iff hi hl]

theorem ind_testBit_rowDiag {i j k l : ℕ} (hj : j < 11) (hl : l < 11) :
    ind ((rowDiag (11 * i + j)).testBit (11 * k + l)) =
      if (i = k ∧ j = l) ∧ i = j then 1 else 0 := by
  unfold rowDiag
  simp only [natDiv_eq, natMod_eq]
  rw [div_eleven hj, mod_eleven hj]
  by_cases hij : i = j
  · have hb : Nat.beq i j = true := by rw [Nat.beq_eq]; exact hij
    rw [hb]
    show ind ((e2 i j).testBit (11 * k + l)) = _
    rw [e2_eq, Nat.testBit_two_pow, ind_decide]
    split_ifs with h1 h2 h2 <;> first | rfl | omega
  · have hb : Nat.beq i j = false := by
      rw [Bool.eq_false_iff, Ne, Nat.beq_eq]
      exact hij
    rw [hb]
    show ind ((0 : ℕ).testBit (11 * k + l)) = _
    simp [ind, hij]

theorem ind_testBit_rowInv (a : List ℕ) {i j k l : ℕ} (hi : i < 11) (hj : j < 11) (hk : k < 11)
    (hl : l < 11) :
    ind ((rowInv a (11 * i + j)).testBit (11 * k + l)) =
      ind ((a.getD i 0).testBit k) * ind ((a.getD j 0).testBit l) +
        (if i = k ∧ j = l then 1 else 0) := by
  unfold rowInv
  simp only [natDiv_eq, natMod_eq, natXor_eq, natMul_eq, natShiftLeft_eq]
  rw [div_eleven hj, mod_eleven hj, Nat.testBit_xor, ind_xor, e2_eq, Nat.testBit_two_pow, ind_decide,
    ind_testBit_xorN]
  simp only [idx_eq_iff hj hl]
  congr 1
  have hterm : ∀ u ∈ Finset.range 11, ind ((bit (col a i) u *
      (col a j <<< (11 * u))).testBit (11 * k + l)) =
      if u = k then ind ((a.getD i 0).testBit k) * ind ((a.getD j 0).testBit l) else 0 := by
    intro u hu
    rw [Finset.mem_range] at hu
    rw [testBit_mulBit, testBit_shiftLeft_field hl (col_lt a j), ind_and, ind_and, testBit_col a i u hu,
      testBit_col a j l hl, ind_decide]
    by_cases huk : u = k
    · subst huk
      simp
    · simp [huk]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range 11) k, if_pos (Finset.mem_range.2 hk)]

end CFSG.KC.CosetJ.F2

end
