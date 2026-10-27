module

public import CFSG.Certificates.Kernel.KStep.Native
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP
open CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371.Native CFSG.KC.MonsterConv.Perm

namespace RhoAux

theorem xorSum_congr {f g : ℕ → Bool} : ∀ {n}, (∀ i < n, f i = g i) → xorSum f n = xorSum g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [xorSum]
    rw [xorSum_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem xorSum_succ (f : ℕ → Bool) : ∀ k, xorSum f (k + 1) = (f 0 ^^ xorSum (fun i => f (i + 1)) k)
  | 0 => by simp [xorSum]
  | k + 1 => by rw [xorSum, xorSum_succ f k, xorSum, Bool.xor_assoc]

theorem xorSum_xor (f g : ℕ → Bool) : ∀ n,
    xorSum (fun i => f i ^^ g i) n = (xorSum f n ^^ xorSum g n)
  | 0 => rfl
  | n + 1 => by
    simp only [xorSum]
    rw [xorSum_xor f g n]
    have h4 : ∀ a b c d : Bool, ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by decide
    exact h4 _ _ _ _

theorem parN_xorSum : ∀ k a, parN k a = xorSum a.testBit k
  | 0, _ => rfl
  | k + 1, a => by
    have ih := parN_xorSum k (a / 2)
    have hf : (fun i => a.testBit (i + 1)) = (a / 2).testBit := funext fun i => Nat.testBit_succ a i
    unfold parN at ih ⊢
    rw [xorSum_succ, hf, ← ih, popcN, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one (popcN k (a / 2)) with h' | h' <;>
      simp [Nat.add_mod, h, h']

theorem pairN_xorSum (a d : ℕ) : pairN a d = xorSum (fun i => a.testBit i && d.testBit i) 12 := by
  unfold pairN
  rw [parN_xorSum]
  exact xorSum_congr fun i _ => Nat.testBit_and a d i

theorem pairN_comm (a d : ℕ) : pairN a d = pairN d a := by
  unfold pairN
  rw [Nat.and_comm]

theorem bitN_eq_toNat (x i : ℕ) : bitN x i = (x.testBit i).toNat := by
  rw [Nat.toNat_testBit]
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem selB_toNat' (b : Bool) (m : ℕ) : selB b.toNat m = if b then m else 0 := by
  cases b
  · exact Nat.zero_mul m
  · exact Nat.one_mul m

theorem testBit_selB_bitN (x i m p : ℕ) :
    (selB (bitN x i) m).testBit p = (x.testBit i && m.testBit p) := by
  rw [bitN_eq_toNat, selB_toNat']
  cases x.testBit i <;> simp

theorem selB_bitN_lt {x i m S : ℕ} (hm : m < 2 ^ S) : selB (bitN x i) m < 2 ^ S := by
  rw [bitN_eq_toNat, selB_toNat']
  cases x.testBit i
  · exact Nat.two_pow_pos S
  · exact hm

theorem testBit_xorLoop (g : ℕ → ℕ) (p : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (g i)) n).testBit p =
      xorSum (fun i => (g i).testBit p) n
  | 0 => by
    change Nat.testBit 0 p = _
    simp [xorSum]
  | n + 1 => by
    change (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (g i)) n ^^^ g n).testBit p = _
    rw [Nat.testBit_xor, testBit_xorLoop g p n]
    rfl

theorem xorLoop_lt (g : ℕ → ℕ) {S : ℕ} (hg : ∀ i, g i < 2 ^ S) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (g i)) n < 2 ^ S
  | 0 => Nat.two_pow_pos S
  | n + 1 => Nat.xor_lt_two_pow (xorLoop_lt g hg n) (hg n)

theorem xorLoop_toNat (g : ℕ → ℕ) (f : ℕ → Bool) : ∀ n, (∀ k < n, g k = (f k).toNat) →
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.xor acc (g k)) n = (xorSum f n).toNat
  | 0, _ => rfl
  | n + 1, h => by
    change Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.xor acc (g k)) n ^^^ g n = _
    rw [xorLoop_toNat g f n (fun k hk => h k (by omega)), h n (by omega)]
    simp only [xorSum]
    cases xorSum f n <;> cases f n <;> rfl

theorem par12_eq (x : ℕ) : par12 x = (parN 12 x).toNat := by
  rw [parN_xorSum]
  exact xorLoop_toNat _ _ 12 fun k _ => bitN_eq_toNat x k

theorem testBit_ones (W q : ℕ) : (ones W).testBit q = decide (q < W) := by
  rw [Benes.ones_eq, Nat.testBit_two_pow_sub_one]

theorem testBit_plane' {S b x p : ℕ} (hp : p < S) :
    (plane S b x).testBit p = x.testBit (b * S + p) := by
  change ((x >>> (b * S)) &&& ones S).testBit p = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, decide_eq_true hp, Bool.and_true]

theorem plane_lt' (S b x : ℕ) : plane S b x < 2 ^ S := by
  change (x >>> (b * S)) &&& ones S < 2 ^ S
  rw [Benes.ones_eq]
  exact Benes.land_ones_lt _ _

theorem SX_eq : SX = 2 ^ 17 := rfl

theorem idPlane_SX {b : ℕ} (hb : b < 17) (p : ℕ) :
    (idPlane SX b).testBit p = (decide (p < SX) && p.testBit b) :=
  Benes.idPlane_testBit (k := 17) hb p

theorem idPlane_SX_lt (b : ℕ) (hb : b < 17) : idPlane SX b < 2 ^ SX :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [idPlane_SX hb, decide_eq_false (by omega), Bool.false_and]

theorem testBit_valW (p : ℕ) : valW.testBit p = decide (p < SX ∧ p % 32 < 24) := by
  change (ones SX ^^^ (idPlane SX 3 &&& idPlane SX 4)).testBit p = _
  rw [Nat.testBit_xor, Nat.testBit_and, testBit_ones, idPlane_SX (by decide), idPlane_SX (by decide)]
  have h3 : p.testBit 3 = (p % 32).testBit 3 := by
    rw [(by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_mod_two_pow]; rfl
  have h4 : p.testBit 4 = (p % 32).testBit 4 := by
    rw [(by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_mod_two_pow]; rfl
  have hm : ∀ x < 32, (x.testBit 3 && x.testBit 4) = decide (24 ≤ x) := by decide
  rw [h3, h4]
  by_cases hp : p < SX
  · rw [decide_eq_true hp, Bool.true_and, Bool.true_and, hm _ (Nat.mod_lt _ (by decide))]
    have e : decide (p < SX ∧ p % 32 < 24) = !decide (24 ≤ p % 32) := by
      by_cases h : 24 ≤ p % 32
      · simp [h]
      · simp [h, hp]
        omega
    rw [e]
    cases decide (24 ≤ p % 32) <;> rfl
  · simp [hp]

theorem valW_lt : valW < 2 ^ SX :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_valW, decide_eq_false (by omega)]

theorem testBit_xorSel {S K m p : ℕ} (hp : p < S) :
    (xorSel S K m).testBit p = xorSum (fun i => m.testBit i && K.testBit (i * S + p)) 12 := by
  refine (testBit_xorLoop (fun i => selB (bitN m i) (plane S i K)) p 12).trans ?_
  exact xorSum_congr fun i _ => by rw [testBit_selB_bitN, testBit_plane' hp]

theorem xorSel_lt (S K m : ℕ) : xorSel S K m < 2 ^ S :=
  xorLoop_lt (fun i => selB (bitN m i) (plane S i K)) (fun i => selB_bitN_lt (plane_lt' S i K)) 12

theorem xorSel_key {K k q : ℕ} (hq : q < 98280)
    (hK : ∀ b < 12, K.testBit (b * SX + xposK q) = k.testBit b) (m : ℕ) :
    (xorSel SX K m).testBit (xposK q) = pairN k m := by
  rw [testBit_xorSel (InitAux.xposK_lt' hq), pairN_xorSum]
  exact xorSum_congr fun i hi => by rw [hK i hi, Bool.and_comm]

theorem xorSel_pad {K p : ℕ} (hp : p < SX) (hK : ∀ b < 12, K.testBit (b * SX + p) = false)
    (m : ℕ) : (xorSel SX K m).testBit p = false := by
  rw [testBit_xorSel hp]
  refine (xorSum_congr (g := fun _ => false) fun i hi => by rw [hK i hi, Bool.and_false]).trans ?_
  clear hK
  induction 12 with
  | zero => rfl
  | succ n ih => simp [xorSum, ih]

theorem xor_split (i a b a' b' : ℕ) (hb : b < 2 ^ i) (hb' : b' < 2 ^ i) :
    (2 ^ i * a + b) ^^^ (2 ^ i * a' + b') = 2 ^ i * (a ^^^ a') + (b ^^^ b') := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hb',
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hb hb'), Nat.testBit_xor, Nat.testBit_xor]
  split_ifs <;> rfl

theorem pos_xor {r j T : ℕ} (hj : j < 32) : (32 * r + j) ^^^ 32 * T = 32 * (r ^^^ T) + j := by
  have := xor_split 5 r j T 0 hj (by decide)
  simp only [Nat.reducePow, Nat.add_zero, Nat.xor_zero] at this
  exact this

theorem pos_xor_mod (p T : ℕ) : (p ^^^ 32 * T) % 32 = p % 32 := by
  have e := Nat.div_add_mod p 32
  have := pos_xor (r := p / 32) (T := T) (Nat.mod_lt p (by decide))
  rw [e] at this
  rw [this]
  omega

theorem pi0N_bit0 (x : ℕ) : (pi0N x).testBit 0 = false := by
  unfold pi0N
  cases h : x.testBit 0
  · rw [ite_eq_right (by simp), Nat.xor_zero, h]
  · rw [ite_eq_left rfl, Nat.testBit_xor, h]
    rfl

theorem pi0N_of_even {x : ℕ} (h : x.testBit 0 = false) : pi0N x = x := by
  unfold pi0N
  rw [ite_eq_right (by simp [h]), Nat.xor_zero]

theorem pi0N_xor_even {m a : ℕ} (h : m.testBit 0 = false) : pi0N (m ^^^ a) = m ^^^ pi0N a := by
  unfold pi0N
  rw [Nat.testBit_xor, h, Bool.false_xor, Nat.xor_assoc]

theorem pi0N_lt {a : ℕ} (ha : a < 4096) : pi0N a < 4096 := by
  unfold pi0N
  have : (if a.testBit 0 = true then 63 else 0) < 2 ^ 12 := by split_ifs <;> decide
  exact Nat.xor_lt_two_pow (n := 12) ha this

theorem two_mul_bit0 (m : ℕ) : (2 * m).testBit 0 = false := by
  rw [Nat.testBit_zero]
  simp

theorem pi0_eq (a : ℕ) : pi0 a = pi0N a := by
  unfold pi0 pi0N
  change a ^^^ 63 * (a &&& 1) = _
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]

@[expose] def rowT (a d : ℕ) : ℕ := 2048 * (pairN 63 d).toNat + pi0N a / 2

theorem rowT_lt {a : ℕ} (ha : a < 4096) (d : ℕ) : rowT a d < 4096 := by
  have := pi0N_lt ha
  unfold rowT
  cases pairN 63 d <;> simp <;> omega

theorem shift_rowC (a r : ℕ) : shiftN a (pi0N (Native.rowC r)) = 2 * (r % 2048) ^^^ pi0N a := by
  unfold shiftN Native.rowC
  rw [pi0N_of_even (two_mul_bit0 _), pi0N_xor_even (two_mul_bit0 _)]

theorem div_two_xor (m a : ℕ) : (2 * m ^^^ a) / 2 = m ^^^ a / 2 := by
  have := Nat.shiftRight_xor_distrib (a := 2 * m) (b := a) (i := 1)
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one] at this
  rw [this, Nat.mul_div_cancel_left _ (by decide)]

theorem xor_pi0N_bit0 (m a : ℕ) : (2 * m ^^^ pi0N a).testBit 0 = false := by
  rw [Nat.testBit_xor, two_mul_bit0, pi0N_bit0]
  rfl

theorem rowIdx_rho {a : ℕ} (ha : a < 4096) (s : Bool) (d : ℕ) {r : ℕ} (hr : r < 4096) :
    Native.rowIdx (ePauliN (s, a, d) (Native.rowEta r) (Native.rowC r)).2.1
      (ePauliN (s, a, d) (Native.rowEta r) (Native.rowC r)).2.2 = r ^^^ rowT a d := by
  have e21 : (ePauliN (s, a, d) (Native.rowEta r) (Native.rowC r)).2.1 =
      (decide (2048 ≤ r) ^^ pairN 63 d) := rfl
  have e22 : (ePauliN (s, a, d) (Native.rowEta r) (Native.rowC r)).2.2 =
      shiftN a (pi0N (Native.rowC r)) := rfl
  rw [e21, e22, shift_rowC]
  unfold Native.rowIdx
  rw [pi0N_of_even (xor_pi0N_bit0 _ _), div_two_xor]
  have h1' : r % 2048 < 2048 := Nat.mod_lt _ (by decide)
  have h1 : r % 2048 < 2 ^ 11 := by simpa using h1'
  have h2 : pi0N a / 2 < 2 ^ 11 := by have := pi0N_lt ha; simp only [Nat.reducePow]; omega
  have h3 := Nat.xor_lt_two_pow h1 h2
  rw [Nat.mod_eq_of_lt (by simpa using h3)]
  have hx := xor_split 11 (r / 2048) (r % 2048) (pairN 63 d).toNat (pi0N a / 2) h1 h2
  simp only [Nat.reducePow] at hx
  rw [Nat.div_add_mod] at hx
  unfold rowT
  rw [hx]
  have hb : r / 2048 = (decide (2048 ≤ r)).toNat := by
    by_cases h : 2048 ≤ r
    · rw [decide_eq_true h]
      simp only [Bool.toNat_true]
      omega
    · rw [decide_eq_false h]
      simp only [Bool.toNat_false]
      omega
  rw [hb]
  cases decide (2048 ≤ r) <;> cases pairN 63 d <;> simp

theorem sign_rho (s : Bool) (a d r : ℕ) :
    (ePauliN (s, a, d) (Native.rowEta r) (Native.rowC r)).1 =
    (s ^^ (decide (2048 ≤ r) && a.testBit 0) ^^
      (xorSum (fun k => (r % 2048).testBit k && d.testBit (k + 1)) 11 ^^
        xorSum (fun i => (pi0N a).testBit i && d.testBit i) 12)) := by
  unfold ePauliN Native.rowEta mu0N
  simp only [Pauli.a, Pauli.d, Pauli.s]
  rw [shift_rowC, pairN_xorSum]
  congr 1
  rw [xorSum_congr (g := fun i => ((2 * (r % 2048)).testBit i && d.testBit i) ^^
    ((pi0N a).testBit i && d.testBit i)) (fun i _ => by rw [Nat.testBit_xor, Bool.and_xor_distrib_right]),
    xorSum_xor, xorSum_succ, two_mul_bit0, Bool.false_and, Bool.false_xor]
  congr 1
  exact xorSum_congr fun k _ => by
    rw [Nat.testBit_succ, Nat.mul_div_cancel_left _ (by decide)]

theorem testBit_pos {r j : ℕ} (hj : j < 32) (k : ℕ) :
    (32 * r + j).testBit (k + 5) = r.testBit k := by
  have := Nat.testBit_two_pow_mul_add r (i := 5) (b := j) (by simpa using hj) (k + 5)
  simp only [Nat.reducePow] at this
  rw [this, ite_eq_right (by omega), Nat.add_sub_cancel]

theorem rhoSgnW_bit {s : Bool} {a d r j : ℕ} (hr : r < 4096) (hj : j < 24) :
    (rhoSgnW s.toNat a d).testBit (32 * r + j) =
      (ePauliN (s, a, d) (Native.rowEta r) (Native.rowC r)).1 := by
  have hP : 32 * r + j < SX := by rw [SX_eq]; omega
  have hpm : (32 * r + j) % 32 < 24 := by omega
  rw [sign_rho]
  unfold rhoSgnW
  change (valW &&& ((selB (s.toNat ^^^ par12 (((pi0 a >>> 1) <<< 1) &&& d)) (ones SX)) ^^^
    ((selB (a &&& 1) (idPlane SX 16)) ^^^
      Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.xor acc
        (selB (bitN d (Nat.add k 1)) (idPlane SX (Nat.add k 5)))) 11))).testBit (32 * r + j) = _
  have e1 : (pi0 a >>> 1) <<< 1 = pi0N a := by
    rw [pi0_eq, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.pow_one]
    have := pi0N_bit0 a
    rw [Nat.testBit_zero] at this
    simp only [decide_eq_false_iff_not] at this
    omega
  have e2 : par12 (pi0N a &&& d) = (xorSum (fun i => (pi0N a).testBit i && d.testBit i) 12).toNat := by
    rw [par12_eq, parN_xorSum]
    congr 1
    exact xorSum_congr fun i _ => Nat.testBit_and _ _ i
  have e3 : s.toNat ^^^ (xorSum (fun i => (pi0N a).testBit i && d.testBit i) 12).toNat =
      (s ^^ xorSum (fun i => (pi0N a).testBit i && d.testBit i) 12).toNat := by
    cases s <;> cases xorSum (fun i => (pi0N a).testBit i && d.testBit i) 12 <;> rfl
  have e4 : a &&& 1 = (a.testBit 0).toNat := by
    rw [Nat.and_one_is_mod, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
  rw [e1, e2, e3, e4, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, testBit_valW,
    decide_eq_true ⟨hP, hpm⟩, Bool.true_and, selB_toNat', selB_toNat',
    testBit_xorLoop (fun k => selB (bitN d (Nat.add k 1)) (idPlane SX (Nat.add k 5)))]
  have e5 : (32 * r + j).testBit 16 = decide (2048 ≤ r) := by
    rw [testBit_pos (by omega) 11]
    exact Benes.testBit_top (b := 11) (by simpa using hr)
  have e6 : xorSum (fun i => (selB (bitN d (Nat.add i 1)) (idPlane SX (Nat.add i 5))).testBit
      (32 * r + j)) 11 = xorSum (fun k => (r % 2048).testBit k && d.testBit (k + 1)) 11 := by
    refine xorSum_congr fun k hk => ?_
    rw [testBit_selB_bitN, idPlane_SX (by simp only [Nat.add_eq]; omega), decide_eq_true hP,
      Bool.true_and]
    simp only [Nat.add_eq]
    rw [testBit_pos (by omega), Bool.and_comm]
    have := Nat.testBit_mod_two_pow r 11 k
    simp only [Nat.reducePow] at this
    rw [this, decide_eq_true hk, Bool.true_and]
  rw [e6]
  have e7 : (if (a.testBit 0 = true) then idPlane SX 16 else 0).testBit (32 * r + j) =
      (decide (2048 ≤ r) && a.testBit 0) := by
    cases a.testBit 0
    · simp
    · simp only [ite_true]
      rw [idPlane_SX (by decide), decide_eq_true hP, Bool.true_and, e5, Bool.and_true]
  rw [e7]
  have e8 : (if (s ^^ xorSum (fun i => (pi0N a).testBit i && d.testBit i) 12) = true then ones SX
      else 0).testBit (32 * r + j) = (s ^^ xorSum (fun i => (pi0N a).testBit i && d.testBit i) 12) := by
    cases (s ^^ xorSum (fun i => (pi0N a).testBit i && d.testBit i) 12)
    · simp
    · simp only [ite_true]
      rw [testBit_ones, decide_eq_true hP]
  rw [e8]
  generalize xorSum (fun i => (pi0N a).testBit i && d.testBit i) 12 = A
  generalize xorSum (fun k => (r % 2048).testBit k && d.testBit (k + 1)) 11 = B
  generalize (decide (2048 ≤ r) && a.testBit 0) = C
  cases s <;> cases A <;> cases B <;> cases C <;> rfl

theorem rhoSgnW_lt (s a d : ℕ) : rhoSgnW s a d < 2 ^ SX := by
  change valW &&& _ < 2 ^ SX
  exact Nat.lt_of_le_of_lt Nat.and_le_left valW_lt

@[expose] noncomputable def trN (O : POps) (S t n y : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun b ih y => CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => Nat) y (O.xsw S b y)
      (Nat.beq (bitN t b) (nat_lit 1))) ih) n y

theorem translG_eq (O : POps) (S t x : ℕ) : translG O S t x = trN O S t 17 x := rfl

theorem trN_succ (O : POps) (S t n y : ℕ) :
    trN O S t (n + 1) y = trN O S t n (if t.testBit n then O.xsw S n y else y) := by
  change CFSG.KC.Loop.strictN _ (fun y => trN O S t n y) = _
  rw [Benes.strictN_eq, bitN_eq_toNat]
  cases t.testBit n <;> rfl

theorem mod_two_pow_succ' (t n : ℕ) :
    t % 2 ^ (n + 1) = t % 2 ^ n ^^^ (if t.testBit n then 2 ^ n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_mod_two_pow]
  have : (if t.testBit n = true then 2 ^ n else 0).testBit i = (t.testBit n && decide (n = i)) := by
    cases t.testBit n
    · simp
    · simp [Nat.testBit_two_pow]
  rw [this]
  rcases Nat.lt_trichotomy i n with h | rfl | h
  · simp [h, show i < n + 1 by omega, show n ≠ i by omega]
  · simp
  · simp [show ¬ i < n + 1 by omega, show ¬ i < n by omega, show n ≠ i by omega]

theorem trN_res {np : ℕ} {O : POps} (hO : PLaw np O) (t : ℕ) : ∀ n ≤ 17, ∀ y, Bd np SX y →
    Bd np SX (trN O SX t n y) ∧
      ∀ p < SX, resPN np SX (trN O SX t n y) p = resPN np SX y (p ^^^ t % 2 ^ n)
  | 0, _, y, hy => ⟨hy, fun p _ => by rw [Nat.pow_zero, Nat.mod_one, Nat.xor_zero]; rfl⟩
  | n + 1, hn, y, hy => by
    rw [trN_succ]
    have hy' : Bd np SX (if t.testBit n then O.xsw SX n y else y) := by
      split_ifs
      · exact hO.xsw_bd SX_eq (by omega) hy
      · exact hy
    obtain ⟨ih1, ih2⟩ := trN_res hO t n (by omega) _ hy'
    refine ⟨ih1, fun p hp => ?_⟩
    have hlt : p ^^^ t % 2 ^ n < SX := by
      rw [SX_eq] at hp ⊢
      exact Nat.xor_lt_two_pow hp (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos n))
        (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [ih2 p hp, mod_two_pow_succ']
    split_ifs
    · rw [hO.xsw_res SX_eq (by omega) hy hlt, Nat.xor_assoc]
    · rw [Nat.xor_zero]

theorem translG_res {np : ℕ} {O : POps} (hO : PLaw np O) {t : ℕ} (ht : t < 2 ^ 17) {y : ℕ}
    (hy : Bd np SX y) :
    Bd np SX (translG O SX t y) ∧ ∀ p < SX, resPN np SX (translG O SX t y) p = resPN np SX y (p ^^^ t) := by
  rw [translG_eq]
  obtain ⟨h1, h2⟩ := trN_res hO t 17 le_rfl y hy
  refine ⟨h1, fun p hp => ?_⟩
  rw [h2 p hp, Nat.mod_eq_of_lt ht]

theorem rho_shift_eq {a : ℕ} (ha : a < 4096) (d : ℕ) :
    Nat.lor (Nat.shiftLeft (Nat.shiftRight (pi0 a) 1) 5) (Nat.shiftLeft (par12 (Nat.land d 63)) 16) =
      32 * rowT a d := by
  have e1 : par12 (Nat.land d 63) = (pairN 63 d).toNat := by
    rw [par12_eq, pairN_comm]
    rfl
  rw [e1, pi0_eq]
  change (pi0N a >>> 1 <<< 5) ||| ((pairN 63 d).toNat <<< 16) = _
  unfold rowT
  have hx : pi0N a / 2 < 2 ^ 11 := by have := pi0N_lt ha; simp only [Nat.reducePow]; omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.pow_one, (by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_two_pow_mul,
    (by rfl : (2048 : ℕ) = 2 ^ 11), Nat.testBit_two_pow_mul_add _ hx]
  generalize (pairN 63 d).toNat = e
  generalize pi0N a / 2 = x at hx
  by_cases h5 : i < 5
  · simp [show ¬ 5 ≤ i by omega, show ¬ 16 ≤ i by omega]
  · by_cases h16 : i < 16
    · simp [show 5 ≤ i by omega, show ¬ 16 ≤ i by omega, show i - 5 < 11 by omega]
    · have hx0 : x.testBit (i - 5) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [show 5 ≤ i by omega, show 16 ≤ i by omega, show ¬ i - 5 < 11 by omega, hx0,
        show i - 5 - 11 = i - 16 by omega]

variable {M : ℕ} {h : ZMod M}

theorem sgnI_mul (b : Bool) (x : ZMod M) : ((sgnI b : ℤ) : ZMod M) * x = if b then -x else x := by
  cases b <;> simp [sgnI]

theorem two_hN {np : ℕ} (hnp : 1 ≤ np) : 2 * hN np = 1 := by
  unfold hN
  rw [← pow_succ', Nat.sub_add_cancel hnp]
  have h0 : ((2 ^ np - 1 : ℕ) : ZMod (2 ^ np - 1)) = 0 := ZMod.natCast_self _
  rw [Nat.cast_sub Nat.one_le_two_pow] at h0
  push_cast at h0
  exact sub_eq_zero.mp h0

theorem xT_rho (hG : KeysGood) (s : Bool) (a d : ℕ) {p : ℕ} (hp : p < 98280) :
    Native.GD.xT (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.rho (s, a, d))) p =
      [(id p, sgnI (pairN (keyQ p).1 d ^^ pairN a (keyQ p).2))] := by
  have hb := hG.1 p hp
  unfold Native.GD.xT
  simp only [Native.GD.ofGen]
  rw [mkCtx_keys hp, fastAct_rho _ hb.1 hb.2]
  dsimp only
  rw [mkCtx_find hG hp]
  rfl

theorem rho_resX (h2 : 2 * h = 1) (hG : KeysGood) (s : Bool) (a d : ℕ) (v : Native.DVec) {q : ℕ}
    (hq : q < 98280) :
    resM h (Native.applyGen (Native.mkCtx ()) (.rho (s, a, d)) v) (300 + q) =
      ((sgnI (pairN (keyQ q).1 d ^^ pairN a (keyQ q).2) : ℤ) : ZMod M) * resM h v (300 + q) := by
  change resM h (Native.applyGD (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.rho (s, a, d)))
    v) (300 + q) = _
  rw [applyGD_resX h2 _ _ _ hq, sum_scat_single (fun p hp => xT_rho hG s a d hp)
    (fun p _ p' _ e => e)]
  have hex : ∃ p < 98280, id p = q := ⟨q, hq, rfl⟩
  rw [dite_eq_left hex]
  have e : hex.choose = q := hex.choose_spec.2
  rw [e]

theorem idG_get {k i : ℕ} (hk : k < 24) (hi : i < 24) :
    (Native.idG ())[k * 24 + i]! = if k = i then 1 else 0 := by
  unfold Native.idG
  rw [getElem!_pos (Array.ofFn _) (k * 24 + i) (by simp; omega), Array.getElem_ofFn]
  have e1 : (k * 24 + i) / 24 = k := by omega
  have e2 : (k * 24 + i) % 24 = i := by omega
  simp only [e1, e2]

theorem idG_sum (f : ℕ → ZMod M) {i : ℕ} (hi : i < 24) :
    ∑ k ∈ Finset.range 24, (((Native.idG ())[k * 24 + i]! : ℤ) : ZMod M) * f k = f i := by
  rw [Finset.sum_eq_single i]
  · rw [idG_get hi hi, ite_eq_left rfl]
    simp
  · intro b hb hne
    rw [idG_get (Finset.mem_range.1 hb) hi, ite_eq_right hne]
    simp
  · intro hn
    exact absurd (Finset.mem_range.2 hi) hn

theorem rho_resA (h2 : 2 * h = 1) (q : Pauli) (v : Native.DVec) {i j : ℕ} (hi : i < 24)
    (hj : j < 24) :
    resM h (Native.applyGen (Native.mkCtx ()) (.rho q) v) (Native.aIdx i j) =
      resM h v (Native.aIdx i j) := by
  change resM h (Native.applyGD (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.rho q))
    v) _ = _
  rw [applyGD_resA h2 _ _ _ (InitAux.aIdx_lt i hi j hj), ListAux.aPos_aIdx i hi j hj]
  have hG : (Native.GD.ofGen (Native.mkCtx ()) (.rho q)).G = Native.idG () := by
    simp only [Native.GD.ofGen]
  have hl : (Native.GD.ofGen (Native.mkCtx ()) (.rho q)).latS = 0 := by simp only [Native.GD.ofGen]
  rw [hG, hl]
  have e : ∀ k, ∑ l ∈ Finset.range 24, (((Native.idG ())[k * 24 + min i j]! : ℤ) : ZMod M) *
      (((Native.idG ())[l * 24 + max i j]! : ℤ) : ZMod M) * resM h v (Native.aIdx k l) =
      (((Native.idG ())[k * 24 + min i j]! : ℤ) : ZMod M) * ∑ l ∈ Finset.range 24,
        (((Native.idG ())[l * 24 + max i j]! : ℤ) : ZMod M) * resM h v (Native.aIdx k l) := by
    intro k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [e]
  rw [idG_sum _ (by omega : min i j < 24), idG_sum _ (by omega : max i j < 24), Nat.mul_zero,
    pow_zero, one_mul]
  rcases le_total i j with hij | hij
  · rw [min_eq_left hij, max_eq_right hij]
  · rw [min_eq_right hij, max_eq_left hij, ListAux.aIdx_comm j hj i hi]

theorem monoRows_get (rm : Bool → ℕ → Bool × Bool × ℕ) {r : ℕ} (hr : r < 4096) :
    (Native.monoRows rm)[r]! = [(Native.rowIdx (rm (Native.rowEta r) (Native.rowC r)).2.1
      (rm (Native.rowEta r) (Native.rowC r)).2.2, sgnI (rm (Native.rowEta r) (Native.rowC r)).1)] := by
  unfold Native.monoRows
  rw [getElem!_pos _ r (by simp; omega)]
  simp

theorem wT_rho {s : Bool} {a : ℕ} (ha : a < 4096) (d : ℕ) {p : ℕ} (hp : p < 98304) :
    (Native.GD.ofGen (Native.mkCtx ()) (.rho (s, a, d))).wT p =
      [((p / 24 ^^^ rowT a d) * 24 + p % 24, sgnI (ePauliN (s, a, d) (Native.rowEta (p / 24))
        (Native.rowC (p / 24))).1)] := by
  unfold Native.GD.wT
  simp only [Native.GD.ofGen]
  rw [monoRows_get _ (by omega), rowIdx_rho ha s d (by omega)]
  rfl

theorem xor_inj {x y T : ℕ} (e : x ^^^ T = y ^^^ T) : x = y := by
  have := congrArg (· ^^^ T) e
  simpa [Nat.xor_assoc] using this

theorem rho_resW (h2 : 2 * h = 1) (s : Bool) {a : ℕ} (ha : a < 4096) (d : ℕ) (v : Native.DVec)
    {r j : ℕ} (hr : r < 4096) (hj : j < 24) :
    resM h (Native.applyGen (Native.mkCtx ()) (.rho (s, a, d)) v) (98580 + 24 * (r ^^^ rowT a d) + j) =
      ((sgnI (ePauliN (s, a, d) (Native.rowEta r) (Native.rowC r)).1 : ℤ) : ZMod M) *
        resM h v (98580 + 24 * r + j) := by
  have hrT : r ^^^ rowT a d < 4096 :=
    Nat.xor_lt_two_pow (n := 12) (by simpa using hr) (by simpa using rowT_lt ha d)
  change resM h (Native.applyGD (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.rho (s, a, d)))
    v) _ = _
  rw [Nat.add_assoc, applyGD_resW h2 _ _ _ (by omega)]
  rw [sum_scat_single (σ := fun p => (p / 24 ^^^ rowT a d) * 24 + p % 24)
    (fun p hp => wT_rho ha d hp) ?inj]
  case inj =>
    intro p hp p' hp' e
    have h1 : p % 24 = p' % 24 := by omega
    have h2 : p / 24 ^^^ rowT a d = p' / 24 ^^^ rowT a d := by omega
    have := xor_inj h2
    omega
  have hex : ∃ p < 98304, (p / 24 ^^^ rowT a d) * 24 + p % 24 = 24 * (r ^^^ rowT a d) + j :=
    ⟨24 * r + j, by omega, by
      rw [show (24 * r + j) / 24 = r by omega, show (24 * r + j) % 24 = j by omega]
      ring⟩
  rw [dite_eq_left hex]
  obtain ⟨hlt, he⟩ := hex.choose_spec
  have hc : hex.choose = 24 * r + j := by
    have h1 : hex.choose % 24 = j := by omega
    have h2 : hex.choose / 24 ^^^ rowT a d = r ^^^ rowT a d := by omega
    have := xor_inj h2
    omega
  rw [hc, show (24 * r + j) / 24 = r by omega, show (24 * r + j) % 24 = j by omega]
  have hG : (Native.GD.ofGen (Native.mkCtx ()) (.rho (s, a, d))).G = Native.idG () := by
    simp only [Native.GD.ofGen]
  have hl : (Native.GD.ofGen (Native.mkCtx ()) (.rho (s, a, d))).latS = 0 := by
    simp only [Native.GD.ofGen]
  have hr0 : (Native.GD.ofGen (Native.mkCtx ()) (.rho (s, a, d))).rowS = 0 := by
    simp only [Native.GD.ofGen]
  rewrite [hG, hl, hr0, Nat.add_zero, pow_zero, one_mul, idG_sum _ hj, Nat.mul_comm r 24]
  rfl

end RhoAux

open RhoAux

theorem rho_sound {np : ℕ} {O : POps} (hO : PLaw np O) (hnp : 2 ≤ np) {F : Fix} (hK : KeyBind F)
    (hG : KeysGood) (s : Bool) {a : ℕ} (ha : a < 4096) (d : ℕ) {v : Native.DVec} {t : St}
    (ht : RepN np v t) (f : Bool) :
    RepN np (Native.applyGen (Native.mkCtx ()) (.rho (s, a, d)) v)
      (f, (rhoG O F s.toNat a d t.2.1 t.2.2.1 t.2.2.2).2) := by
  obtain ⟨hX1, hX2, hX3, hA1, hA2, hA3, hW1, hW2, hW3⟩ := ht
  have h2 := two_hN (np := np) (by omega)
  have hSX : SX = 131072 := rfl
  have hm : Nat.xor (xorSel SX F.keyA d) (xorSel SX F.keyD a) < 2 ^ SX :=
    Nat.xor_lt_two_pow (xorSel_lt _ _ _) (xorSel_lt _ _ _)
  have hWs := hO.neg_bd (rhoSgnW_lt s.toNat a d) hW3
  have htl : 32 * rowT a d < 2 ^ 17 := by have := rowT_lt ha d; simp only [Nat.reducePow]; omega
  obtain ⟨hT1, hT2⟩ := translG_res hO htl hWs
  have e : (f, (rhoG O F s.toNat a d t.2.1 t.2.2.1 t.2.2.2).2) = (f, O.neg SX
      (Nat.xor (xorSel SX F.keyA d) (xorSel SX F.keyD a)) t.2.1, t.2.2.1,
      translG O SX (32 * rowT a d) (O.neg SX (rhoSgnW s.toNat a d) t.2.2.2)) := by
    change (f, O.neg SX (Nat.xor (xorSel SX F.keyA d) (xorSel SX F.keyD a)) t.2.1, t.2.2.1,
      translG O SX (Nat.lor (Nat.shiftLeft (Nat.shiftRight (pi0 a) 1) 5)
        (Nat.shiftLeft (par12 (Nat.land d 63)) 16)) (O.neg SX (rhoSgnW s.toNat a d) t.2.2.2)) = _
    rw [rho_shift_eq ha]
  rw [e]
  unfold RepN
  refine ⟨fun q hq => ?_, fun p hp hq => ?_, hO.neg_bd hm hX3, fun i hi j hj => ?_, hA2, hA3,
    fun r' hr' j hj => ?_, fun p hp hpm => ?_, hT1⟩
  · change resPN np SX (O.neg SX _ t.2.1) (xposK q) = resM (hN np) _ (300 + q)
    have hk := hG.1 q hq
    rw [hO.neg_res hm hX3 (InitAux.xposK_lt' hq), rho_resX h2 hG s a d v hq, sgnI_mul,
      hX1 q hq]
    change (if (xorSel SX F.keyA d ^^^ xorSel SX F.keyD a).testBit (xposK q) = true then _ else _) = _
    rw [Nat.testBit_xor, xorSel_key hq (hK.ka q hq) d, xorSel_key hq (hK.kd q hq) a,
      pairN_comm (keyQ q).2 a]
    rfl
  · change resPN np SX (O.neg SX _ t.2.1) p = 0
    rw [hO.neg_res hm hX3 hp, hX2 p hp hq]
    simp
  · change resPN np SA t.2.2.1 (32 * i + j) = resM (hN np) _ (Native.aIdx i j)
    rw [rho_resA h2 _ v hi hj]
    exact hA1 i hi j hj
  · have hrT := rowT_lt ha d
    have hr : r' ^^^ rowT a d < 4096 :=
      Nat.xor_lt_two_pow (n := 12) (by simpa using hr') (by simpa using hrT)
    have hrr : (r' ^^^ rowT a d) ^^^ rowT a d = r' := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    change resPN np SX (translG O SX (32 * rowT a d) _) (32 * r' + j) = resM (hN np) _ _
    have hP : 32 * r' + j < SX := by rw [hSX]; omega
    have hP' : 32 * (r' ^^^ rowT a d) + j < SX := by rw [hSX]; omega
    rw [hT2 _ hP, pos_xor (by omega), hO.neg_res (rhoSgnW_lt _ _ _) hW3 hP',
      rhoSgnW_bit hr hj, hW1 _ hr j hj]
    have := rho_resW h2 s ha d v hr hj (h := hN np)
    rw [hrr] at this
    rw [this, sgnI_mul]
    rfl
  · change resPN np SX (translG O SX (32 * rowT a d) _) p = 0
    have hp' : p ^^^ 32 * rowT a d < SX := by
      rw [SX_eq] at hp ⊢
      exact Nat.xor_lt_two_pow hp htl
    rw [hT2 _ hp, hO.neg_res (rhoSgnW_lt _ _ _) hW3 hp',
      hW2 _ hp' (by rw [pos_xor_mod]; exact hpm)]
    simp

end CFSG.KC.KStep

end
