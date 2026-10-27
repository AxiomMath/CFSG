module

public import CFSG.Certificates.Kernel.KStep.Native
public import CFSG.Certificates.Kernel.KStep.Laws
public import CFSG.Certificates.Kernel.Trace6091.TwinEq
public import CFSG.Monster.B.Rep4371.GlueDefs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP
open CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371.Native CFSG.KC.MonsterConv.Perm

namespace PermAux

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

theorem xorSum_false : ∀ n, xorSum (fun _ => false) n = false
  | 0 => rfl
  | n + 1 => by simp [xorSum, xorSum_false n]

theorem xorSum_single (g : ℕ → Bool) (c0 : ℕ) : ∀ n,
    xorSum (fun c => decide (c = c0) && g c) n = (decide (c0 < n) && g c0)
  | 0 => by simp [xorSum]
  | n + 1 => by
    simp only [xorSum]
    rw [xorSum_single g c0 n]
    by_cases h : n = c0
    · subst h
      simp
    · have : (c0 < n + 1) ↔ c0 < n := by omega
      simp [h, this]

theorem and_xorSum (b : Bool) (f : ℕ → Bool) : ∀ n, (b && xorSum f n) = xorSum (fun j => b && f j) n
  | 0 => by simp [xorSum]
  | n + 1 => by
    simp only [xorSum]
    rw [← and_xorSum b f n, Bool.and_xor_distrib_left]

theorem xorSum_guard (g : ℕ → Bool) (N : ℕ) : ∀ n,
    xorSum (fun m => decide (m < N) && g m) n = xorSum g (min n N)
  | 0 => by simp [xorSum]
  | n + 1 => by
    simp only [xorSum]
    rw [xorSum_guard g N n]
    by_cases h : n < N
    · rw [show min (n + 1) N = min n N + 1 by omega, show min n N = n by omega, decide_eq_true h,
        Bool.true_and]
      rfl
    · rw [show min (n + 1) N = min n N by omega, decide_eq_false h, Bool.false_and, Bool.xor_false]

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

theorem bitN_eq_toNat (x i : ℕ) : bitN x i = (x.testBit i).toNat := by
  rw [Nat.toNat_testBit]
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem selB_toNat' (b : Bool) (m : ℕ) : selB b.toNat m = if b then m else 0 := by
  cases b
  · exact Nat.zero_mul m
  · exact Nat.one_mul m

theorem testBit_selB_toNat (b : Bool) (m p : ℕ) : (selB b.toNat m).testBit p = (b && m.testBit p) := by
  rw [selB_toNat']
  cases b <;> simp

theorem testBit_selB_bitN (x i m p : ℕ) :
    (selB (bitN x i) m).testBit p = (x.testBit i && m.testBit p) := by
  rw [bitN_eq_toNat, testBit_selB_toNat]

theorem selB_toNat_lt {b : Bool} {m S : ℕ} (hm : m < 2 ^ S) : selB b.toNat m < 2 ^ S := by
  rw [selB_toNat']
  cases b
  · exact Nat.two_pow_pos S
  · exact hm

theorem blt_toNat (i j : ℕ) : Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt i j) = (decide (i < j)).toNat := by
  have h : Nat.blt i j = decide (i < j) := Bool.eq_iff_iff.mpr (by simp [Nat.blt_eq])
  rw [h]
  cases decide (i < j) <;> rfl

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

theorem testBit_orLoop' (g : ℕ → ℕ) (t : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.lor acc (g k)) n).testBit t =
      decide (∃ k < n, (g k).testBit t = true) := by
  intro n
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact Trace6091.testBit_orLoop g t n

theorem testBit_ones (W q : ℕ) : (ones W).testBit q = decide (q < W) := by
  rw [Benes.ones_eq, Nat.testBit_two_pow_sub_one]

theorem ones_lt (W : ℕ) : ones W < 2 ^ W := by
  rw [Benes.ones_eq]
  exact Nat.sub_lt (Nat.two_pow_pos W) Nat.one_pos

theorem testBit_plane' {S b x p : ℕ} (hp : p < S) :
    (plane S b x).testBit p = x.testBit (b * S + p) := by
  change ((x >>> (b * S)) &&& ones S).testBit p = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, decide_eq_true hp, Bool.and_true]

theorem plane_lt' (S b x : ℕ) : plane S b x < 2 ^ S := by
  change (x >>> (b * S)) &&& ones S < 2 ^ S
  rw [Benes.ones_eq]
  exact Benes.land_ones_lt _ _

theorem SX_eq : SX = 2 ^ 17 := rfl

theorem SA_eq : SA = 2 ^ 10 := rfl

theorem idPlane_SX {b : ℕ} (hb : b < 17) (p : ℕ) :
    (idPlane SX b).testBit p = (decide (p < SX) && p.testBit b) :=
  Benes.idPlane_testBit (k := 17) hb p

theorem idPlane_SA {b : ℕ} (hb : b < 10) (p : ℕ) :
    (idPlane SA b).testBit p = (decide (p < SA) && p.testBit b) :=
  Benes.idPlane_testBit (k := 10) hb p

theorem idPlane_lt' {k b : ℕ} (hb : b < k) : idPlane (2 ^ k) b < 2 ^ 2 ^ k :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [Benes.idPlane_testBit hb, decide_eq_false (by omega), Bool.false_and]

theorem testBit_mod32 (p : ℕ) {b : ℕ} (hb : b < 5) : p.testBit b = (p % 32).testBit b := by
  rw [(by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_mod_two_pow, decide_eq_true hb, Bool.true_and]

theorem bits34 : ∀ x < 32, (x.testBit 3 && x.testBit 4) = decide (24 ≤ x) := by decide

theorem testBit_valW (p : ℕ) : valW.testBit p = decide (p < SX ∧ p % 32 < 24) := by
  change (ones SX ^^^ (idPlane SX 3 &&& idPlane SX 4)).testBit p = _
  rw [Nat.testBit_xor, Nat.testBit_and, testBit_ones, idPlane_SX (by decide), idPlane_SX (by decide),
    testBit_mod32 p (b := 3) (by decide), testBit_mod32 p (b := 4) (by decide)]
  by_cases hp : p < SX
  · rw [decide_eq_true hp, Bool.true_and, Bool.true_and, bits34 _ (Nat.mod_lt _ (by decide))]
    by_cases h : 24 ≤ p % 32
    · simp [h]
    · have : p % 32 < 24 := by omega
      simp [h, hp, this]
  · simp [hp]

theorem valW_lt : valW < 2 ^ SX :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_valW, decide_eq_false (by omega)]

theorem testBit_valA (p : ℕ) : valA.testBit p = decide (p < SA ∧ p % 32 < 24 ∧ p / 32 < 24) := by
  change ((ones SA ^^^ (idPlane SA 3 &&& idPlane SA 4)) &&&
    (ones SA ^^^ (idPlane SA 8 &&& idPlane SA 9))).testBit p = _
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, testBit_ones,
    idPlane_SA (by decide), idPlane_SA (by decide), idPlane_SA (by decide), idPlane_SA (by decide),
    testBit_mod32 p (b := 3) (by decide), testBit_mod32 p (b := 4) (by decide)]
  by_cases hp : p < SA
  · have h8 : p.testBit 8 = (p / 32).testBit 3 := by
      rw [(by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_div_two_pow]
    have h9 : p.testBit 9 = (p / 32).testBit 4 := by
      rw [(by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_div_two_pow]
    have hd : p / 32 < 32 := by rw [SA_eq] at hp; simp only [Nat.reducePow] at hp; omega
    simp only [h8, h9, decide_eq_true hp, Bool.true_and]
    rw [bits34 _ (Nat.mod_lt _ (by decide)), bits34 _ hd]
    by_cases h1 : 24 ≤ p % 32 <;> by_cases h2 : 24 ≤ p / 32 <;> simp [h1, h2, hp] <;> omega
  · simp [hp]

theorem valA_lt : valA < 2 ^ SA :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_valA, decide_eq_false (by omega)]

theorem testBit_shl_plane {S x c b p : ℕ} (hx : x < 2 ^ S) (hp : p < S) :
    (Nat.shiftLeft x (c * S)).testBit (b * S + p) = (decide (c = b) && x.testBit p) := by
  change (x <<< (c * S)).testBit (b * S + p) = _
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy c b with h | rfl | h
  · have h1 : (c + 1) * S ≤ b * S := Nat.mul_le_mul_right S h
    rw [Nat.succ_mul] at h1
    have h2 : x.testBit (b * S + p - c * S) = false :=
      Nat.testBit_lt_two_pow (Benes.lt_two_pow_mono hx (by omega))
    rw [h2]
    simp [show c ≠ b by omega]
  · simp
  · have h1 : (b + 1) * S ≤ c * S := Nat.mul_le_mul_right S h
    rw [Nat.succ_mul] at h1
    rw [decide_eq_false (by omega), decide_eq_false (by omega)]
    simp

theorem shl_plane_lt {S x c n : ℕ} (hx : x < 2 ^ S) (hc : c < n) :
    Nat.shiftLeft x (c * S) < 2 ^ (n * S) := by
  change x <<< (c * S) < _
  rw [Nat.shiftLeft_eq]
  have h1 : (c + 1) * S ≤ n * S := Nat.mul_le_mul_right S hc
  calc x * 2 ^ (c * S) < 2 ^ S * 2 ^ (c * S) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
    _ = 2 ^ ((c + 1) * S) := by rw [← Nat.pow_add, Nat.succ_mul, Nat.add_comm]
    _ ≤ 2 ^ (n * S) := Nat.pow_le_pow_right (by decide) h1

theorem testBit_planeLoop {S n : ℕ} (h sh : ℕ → ℕ) (hsh : ∀ k, sh k = k * S)
    (hh : ∀ k < n, h k < 2 ^ S) {b p : ℕ} (hb : b < n) (hp : p < S) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.lor acc (Nat.shiftLeft (h k) (sh k))) n).testBit
      (b * S + p) = (h b).testBit p := by
  rw [testBit_orLoop']
  simp only [hsh]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨k, hk, e⟩
    rw [testBit_shl_plane (hh k hk) hp, Bool.and_eq_true, decide_eq_true_iff] at e
    rw [← e.1]
    exact e.2
  · intro e
    exact ⟨b, hb, by rw [testBit_shl_plane (hh b hb) hp]; simp [e]⟩

theorem orLoop_lt (g : ℕ → ℕ) {W : ℕ} (hg : ∀ k, k < W → g k < 2 ^ W) : ∀ n, n ≤ W →
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.lor acc (g k)) n < 2 ^ W
  | 0, _ => Nat.two_pow_pos W
  | n + 1, hn => Nat.or_lt_two_pow (orLoop_lt g hg n (by omega)) (hg n (by omega))

theorem planeLoop_lt {S n : ℕ} (h sh : ℕ → ℕ) (hsh : ∀ k, sh k = k * S)
    (hh : ∀ k < n, h k < 2 ^ S) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.lor acc (Nat.shiftLeft (h k) (sh k))) n <
      2 ^ (n * S) := by
  have key : ∀ m ≤ n, Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => Nat.lor acc (Nat.shiftLeft (h k) (sh k))) m < 2 ^ (n * S) := by
    intro m
    induction m with
    | zero => intro _; exact Nat.two_pow_pos _
    | succ m ih =>
      intro hm
      change Nat.rec (motive := fun _ => ℕ) 0
        (fun k acc => Nat.lor acc (Nat.shiftLeft (h k) (sh k))) m ||| Nat.shiftLeft (h m) (sh m) < _
      rw [hsh]
      exact Nat.or_lt_two_pow (ih (by omega)) (shl_plane_lt (hh m (by omega)) (by omega))
  exact key n le_rfl

@[expose] def Holds (n S X p x : ℕ) : Prop := ∀ b < n, X.testBit (b * S + p) = x.testBit b

theorem holds_xor {n S X Y p x y : ℕ} (hX : Holds n S X p x) (hY : Holds n S Y p y) :
    Holds n S (Nat.xor X Y) p (x ^^^ y) := fun b hb => by
  change (X ^^^ Y).testBit _ = _
  rw [Nat.testBit_xor, Nat.testBit_xor, hX b hb, hY b hb]

theorem holds_eq {n S X p x y : ℕ} (hx : Holds n S X p x) (hy : Holds n S X p y) (hxl : x < 2 ^ n)
    (hyl : y < 2 ^ n) : x = y :=
  Nat.eq_of_testBit_eq fun b => by
    by_cases hb : b < n
    · rw [← hx b hb, hy b hb]
    · rw [Nat.testBit_lt_two_pow (Benes.lt_two_pow_mono hxl (by omega)),
        Nat.testBit_lt_two_pow (Benes.lt_two_pow_mono hyl (by omega))]

theorem testBit_split12 {S A D x u : ℕ} (hA : A < 2 ^ (12 * S)) (hx : x < S) :
    (Nat.lor A (Nat.shiftLeft D (Nat.mul 12 S))).testBit (u * S + x) =
      if u < 12 then A.testBit (u * S + x) else D.testBit ((u - 12) * S + x) := by
  change (A ||| D <<< (12 * S)).testBit _ = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  split_ifs with hu
  · have h1 : (u + 1) * S ≤ 12 * S := Nat.mul_le_mul_right S hu
    rw [Nat.succ_mul] at h1
    rw [decide_eq_false (by omega), Bool.false_and, Bool.or_false]
  · have h1 : 12 * S ≤ u * S := Nat.mul_le_mul_right S (by omega)
    have e : u * S + x - 12 * S = (u - 12) * S + x := by rw [Nat.sub_mul]; omega
    rw [Nat.testBit_lt_two_pow (Benes.lt_two_pow_mono hA (by omega)), Bool.false_or,
      decide_eq_true (by omega), Bool.true_and, e]

theorem testBit_combN (m : ℕ → ℕ) (a k : ℕ) : ∀ n,
    (combN m n a).testBit k = xorSum (fun i => a.testBit i && (m i).testBit k) n
  | 0 => by simp [combN, xorSum]
  | n + 1 => by
    simp only [combN, xorSum]
    rw [Nat.testBit_xor, testBit_combN m a k n]
    cases a.testBit n <;> simp

theorem testBit_packN (f : ℕ → Bool) (k : ℕ) : ∀ n, (packN f n).testBit k = (decide (k < n) && f k)
  | 0 => by simp [packN]
  | n + 1 => by
    simp only [packN]
    rw [Nat.testBit_or, testBit_packN f k n]
    have : (if f n = true then 2 ^ n else 0).testBit k = (decide (n = k) && f n) := by
      cases f n
      · simp
      · simp [Nat.testBit_two_pow]
    rw [this]
    rcases Nat.lt_trichotomy k n with h | rfl | h
    · simp [h, show k < n + 1 by omega, show n ≠ k by omega]
    · simp
    · simp [show ¬ k < n + 1 by omega, show ¬ k < n by omega, show n ≠ k by omega]

theorem packN_lt (f : ℕ → Bool) (n : ℕ) : packN f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by rw [testBit_packN, decide_eq_false (by omega)]; rfl

theorem combN_xor (m : ℕ → ℕ) (n x y : ℕ) : combN m n (x ^^^ y) = combN m n x ^^^ combN m n y :=
  Nat.eq_of_testBit_eq fun k => by
    rw [Nat.testBit_xor, testBit_combN, testBit_combN, testBit_combN, ← xorSum_xor]
    exact xorSum_congr fun i _ => by rw [Nat.testBit_xor, Bool.and_xor_distrib_right]

theorem combN_zero (m : ℕ → ℕ) (n : ℕ) : combN m n 0 = 0 :=
  Nat.eq_of_testBit_eq fun k => by
    rw [testBit_combN, Nat.zero_testBit]
    exact (xorSum_congr fun i _ => by simp).trans (xorSum_false n)

theorem combN_congr {m m' : ℕ → ℕ} (a : ℕ) : ∀ {n}, (∀ i < n, m i = m' i) → combN m n a = combN m' n a
  | 0, _ => rfl
  | n + 1, h => by
    simp only [combN]
    rw [combN_congr a (fun i hi => h i (by omega)), h n (by omega)]

theorem combN_map {L : ℕ → ℕ} (hL : ∀ x y, L (x ^^^ y) = L x ^^^ L y) (h0 : L 0 = 0) (m : ℕ → ℕ)
    (a : ℕ) : ∀ n, L (combN m n a) = combN (fun i => L (m i)) n a
  | 0 => by simp [combN, h0]
  | n + 1 => by
    simp only [combN]
    rw [hL, combN_map hL h0 m a n]
    cases a.testBit n
    · simp [h0]
    · simp

theorem combN_and (m : ℕ → ℕ) (a c : ℕ) : ∀ n, combN m n a &&& c = combN (fun i => m i &&& c) n a
  | 0 => by simp [combN]
  | n + 1 => by
    simp only [combN]
    rw [Nat.and_xor_distrib_right, combN_and m a c n]
    cases a.testBit n <;> simp

theorem combN_two_pow (m : ℕ → ℕ) (i : ℕ) : ∀ n, combN m n (2 ^ i) = if i < n then m i else 0
  | 0 => by simp [combN]
  | n + 1 => by
    simp only [combN]
    rw [combN_two_pow m i n, Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy i n with h | rfl | h
    · simp [h, show i < n + 1 by omega, show i ≠ n by omega]
    · simp
    · simp [show ¬ i < n + 1 by omega, show ¬ i < n by omega, show i ≠ n by omega]

theorem parN_xor (k x y b : ℕ) : parN k ((x ^^^ y) &&& b) = (parN k (x &&& b) ^^ parN k (y &&& b)) := by
  rw [parN_xorSum, parN_xorSum, parN_xorSum, ← xorSum_xor]
  exact xorSum_congr fun i _ => by
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Bool.and_xor_distrib_right]

theorem parN_zero (k b : ℕ) : parN k (0 &&& b) = false := by
  rw [parN_xorSum, Nat.zero_and]
  exact (xorSum_congr fun i _ => by simp).trans (xorSum_false k)

theorem packPar_xor (u : ℕ → ℕ) (x y : ℕ) :
    packN (fun k => parN 24 ((x ^^^ y) &&& u k)) 12 =
      packN (fun k => parN 24 (x &&& u k)) 12 ^^^ packN (fun k => parN 24 (y &&& u k)) 12 :=
  Nat.eq_of_testBit_eq fun k => by
    rw [Nat.testBit_xor, testBit_packN, testBit_packN, testBit_packN, parN_xor]
    cases decide (k < 12) <;> simp

theorem packPar_zero (u : ℕ → ℕ) : packN (fun k => parN 24 (0 &&& u k)) 12 = 0 :=
  Nat.eq_of_testBit_eq fun k => by
    rw [testBit_packN, parN_zero]
    simp

theorem dualN_xor (x y : ℕ) : dualN (x ^^^ y) = dualN x ^^^ dualN y := packPar_xor bmaskN x y

theorem dualN_zero : dualN 0 = 0 := packPar_zero bmaskN

theorem coeffN_xor (x y : ℕ) : coeffN (x ^^^ y) = coeffN x ^^^ coeffN y := packPar_xor umaskN x y

theorem coeffN_zero : coeffN 0 = 0 := packPar_zero umaskN

theorem permWordN_xor (p : Array ℕ) (x y : ℕ) :
    permWordN p (x ^^^ y) = permWordN p x ^^^ permWordN p y := combN_xor _ _ _ _

theorem permWordN_zero (p : Array ℕ) : permWordN p 0 = 0 := combN_zero _ _

theorem coeffN_lt (w : ℕ) : coeffN w < 4096 := packN_lt _ 12

theorem dualN_lt (w : ℕ) : dualN w < 4096 := packN_lt _ 12

theorem permCN_lt (p : Array ℕ) (a : ℕ) : permCN p a < 4096 := coeffN_lt _

theorem permDN_lt (p : Array ℕ) (d : ℕ) : permDN p d < 4096 := dualN_lt _

theorem permCN_lin (p : Array ℕ) (a : ℕ) : permCN p a = combN (fun i => permCN p (2 ^ i)) 12 a := by
  have hL : ∀ x y, coeffN (permWordN p (x ^^^ y)) = coeffN (permWordN p x) ^^^ coeffN (permWordN p y) :=
    fun x y => by rw [permWordN_xor, coeffN_xor]
  have h0 : coeffN (permWordN p 0) = 0 := by rw [permWordN_zero, coeffN_zero]
  have e := combN_map (L := fun x => coeffN (permWordN p x)) hL h0 bmaskN a 12
  refine e.trans (combN_congr a fun i hi => ?_)
  change coeffN (permWordN p (bmaskN i)) = coeffN (permWordN p (combN bmaskN 12 (2 ^ i)))
  rw [combN_two_pow, ite_eq_left hi]

theorem permDN_lin (p : Array ℕ) (d : ℕ) : permDN p d = combN (fun i => permDN p (2 ^ i)) 12 d := by
  have hL : ∀ x y, dualN (permWordN p (x ^^^ y)) = dualN (permWordN p x) ^^^ dualN (permWordN p y) :=
    fun x y => by rw [permWordN_xor, dualN_xor]
  have h0 : dualN (permWordN p 0) = 0 := by rw [permWordN_zero, dualN_zero]
  have e := combN_map (L := fun x => dualN (permWordN p x)) hL h0 umaskN d 12
  refine e.trans (combN_congr d fun i hi => ?_)
  change dualN (permWordN p (umaskN i)) = dualN (permWordN p (combN umaskN 12 (2 ^ i)))
  rw [combN_two_pow, ite_eq_left hi]

theorem thetaRec_bit (x k : ℕ) : ∀ N, (thetaRec N x).testBit k = xorSum (fun n => x.testBit n &&
    ((packN (betaN n) 12).testBit k ^^
      xorSum (fun m => x.testBit m && (dualN (bmaskN m &&& bmaskN n)).testBit k) n)) N
  | 0 => by simp [thetaRec, xorSum]
  | N + 1 => by
    simp only [thetaRec, xorSum]
    rw [← thetaRec_bit x k N]
    have e : dualN (combN bmaskN N x &&& bmaskN N) = combN (fun m => dualN (bmaskN m &&& bmaskN N)) N x := by
      rw [combN_and, combN_map dualN_xor dualN_zero]
    split_ifs with h
    · rw [Nat.testBit_xor, Nat.testBit_xor, e, testBit_combN, h, Bool.true_and, Bool.xor_assoc]
    · rw [Bool.not_eq_true] at h
      rw [h, Bool.false_and, Bool.xor_false]

theorem thetaRec_lt (x : ℕ) : ∀ N, thetaRec N x < 4096
  | 0 => by simp [thetaRec]
  | N + 1 => by
    simp only [thetaRec]
    split_ifs
    · exact Nat.xor_lt_two_pow (n := 12) (Nat.xor_lt_two_pow (thetaRec_lt x N) (packN_lt _ 12))
        (dualN_lt _)
    · exact thetaRec_lt x N

theorem thetaN_lt (x : ℕ) : thetaN x < 4096 := thetaRec_lt x 12

theorem thetaN_zero : thetaN 0 = 0 :=
  Nat.eq_of_testBit_eq fun k => by
    unfold thetaN
    rw [thetaRec_bit, Nat.zero_testBit]
    exact (xorSum_congr fun i _ => by simp).trans (xorSum_false 12)

theorem testBit_basisImg {f : ℕ → ℕ} (hf : ∀ i < 12, f (2 ^ i) < 2 ^ 12) {i k : ℕ} (hi : i < 12)
    (hk : k < 12) : (basisImg f).testBit (12 * i + k) = (f (2 ^ i)).testBit k := by
  unfold basisImg
  rw [Nat.mul_comm 12 i]
  refine (testBit_planeLoop (S := 12) (n := 12) (fun i => f (Nat.shiftLeft 1 i))
    (fun i => Nat.mul 12 i) (fun k => Nat.mul_comm 12 k) (fun k hk => ?_) hi hk).trans ?_
  · rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]
    exact hf k hk
  · rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]

theorem plinRow_lt (S MI X k : ℕ) : Nat.rec (motive := fun _ => ℕ) 0 (fun i acc2 => Nat.xor acc2
    (selB (bitN MI (Nat.add (Nat.mul 12 i) k)) (plane S i X))) 12 < 2 ^ S :=
  xorLoop_lt (fun i => selB (bitN MI (Nat.add (Nat.mul 12 i) k)) (plane S i X))
    (fun i => by rw [bitN_eq_toNat]; exact selB_toNat_lt (plane_lt' S i X)) 12

theorem holds_plin {S X p x : ℕ} {f : ℕ → ℕ} (hp : p < S) (hf : ∀ i < 12, f (2 ^ i) < 2 ^ 12)
    (hX : Holds 12 S X p x) :
    Holds 12 S (plin S (basisImg f) X) p (combN (fun i => f (2 ^ i)) 12 x) := fun k hk => by
  unfold plin
  refine (testBit_planeLoop (n := 12) (fun k => Nat.rec (motive := fun _ => ℕ) 0 (fun i acc2 => Nat.xor acc2
      (selB (bitN (basisImg f) (Nat.add (Nat.mul 12 i) k)) (plane S i X))) 12)
    (fun k => Nat.mul k S) (fun _ => rfl) (fun k _ => plinRow_lt S _ X k) hk hp).trans ?_
  refine (testBit_xorLoop (fun i => selB (bitN (basisImg f) (Nat.add (Nat.mul 12 i) k)) (plane S i X))
    p 12).trans ?_
  rw [testBit_combN]
  exact xorSum_congr fun i hi => by
    rw [testBit_selB_bitN, testBit_plane' hp, hX i hi]
    change ((basisImg f).testBit (12 * i + k) && _) = _
    rw [testBit_basisImg hf hi hk, Bool.and_comm]

theorem plin_lt (S MI X : ℕ) : plin S MI X < 2 ^ (12 * S) :=
  planeLoop_lt (n := 12) (fun k => Nat.rec (motive := fun _ => ℕ) 0 (fun i acc2 => Nat.xor acc2
      (selB (bitN MI (Nat.add (Nat.mul 12 i) k)) (plane S i X))) 12)
    (fun k => Nat.mul k S) (fun _ => rfl) (fun k _ => plinRow_lt S MI X k)

theorem testBit_repP {S n m b p : ℕ} (hm : m < 2 ^ S) (hb : b < n) (hp : p < S) :
    (repP S n m).testBit (b * S + p) = m.testBit p :=
  testBit_planeLoop (fun _ => m) (fun k => Nat.mul k S) (fun _ => rfl) (fun _ _ => hm) hb hp

theorem testBit_constP {S c m k p : ℕ} (hm : m < 2 ^ S) (hk : k < 12) (hp : p < S) :
    (constP S c m).testBit (k * S + p) = (c.testBit k && m.testBit p) := by
  unfold constP
  refine (testBit_planeLoop (n := 12) (fun k => selB (bitN c k) m) (fun k => Nat.mul k S) (fun _ => rfl)
    (fun k _ => by rw [bitN_eq_toNat]; exact selB_toNat_lt hm) hk hp).trans ?_
  rw [testBit_selB_bitN]

@[expose] noncomputable def thetaInner (S X n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun m acc2 => Nat.xor acc2
    (selB (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt m n))
      (constP S (dualT (Nat.land (bmT m) (bmT n))) (plane S m X)))) 12

theorem holds_thetaPl {S X p x : ℕ} (hp : p < S) (hX : Holds 12 S X p x) :
    Holds 12 S (thetaPl S X) p (thetaN x) := fun k hk => by
  unfold thetaPl thetaN
  refine (testBit_xorLoop (fun n => Nat.land (repP S 12 (plane S n X))
    (Nat.xor (constP S (packBetaT n) (ones S)) (thetaInner S X n))) (k * S + p) 12).trans ?_
  rw [thetaRec_bit]
  refine xorSum_congr fun n hn => ?_
  change ((repP S 12 (plane S n X)) &&& (constP S (packBetaT n) (ones S) ^^^
    thetaInner S X n)).testBit (k * S + p) = _
  rw [Nat.testBit_and, Nat.testBit_xor, testBit_repP (plane_lt' S n X) hk hp, testBit_plane' hp,
    hX n hn, testBit_constP (ones_lt S) hk hp, testBit_ones, decide_eq_true hp, Bool.and_true]
  have h1 : (packBetaT n).testBit k = (packN (betaN n) 12).testBit k := by
    rw [Trace6091.packBetaT_eq n hn, ← CFSG.Monster.B.Rep4371.native_packN,
      ← CFSG.Monster.B.Rep4371.native_betaN]
  have hg := xorSum_guard (fun m => x.testBit m && (dualN (bmaskN m &&& bmaskN n)).testBit k) n 12
  rw [Nat.min_eq_right hn.le] at hg
  rw [h1, ← hg]
  unfold thetaInner
  rw [testBit_xorLoop (fun m => selB (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt m n))
      (constP S (dualT (Nat.land (bmT m) (bmT n))) (plane S m X)))]
  refine congrArg _ (congrArg _ (xorSum_congr fun m hm => ?_))
  rw [blt_toNat, testBit_selB_toNat, testBit_constP (plane_lt' S m X) hk hp, testBit_plane' hp, hX m hm,
    Trace6091.dualT_eq, Benes.nland, Trace6091.bmT_eq m hm, Trace6091.bmT_eq n hn,
    ← CFSG.Monster.B.Rep4371.native_dualN, ← CFSG.Monster.B.Rep4371.native_bmaskN]
  cases x.testBit m <;> cases decide (m < n) <;> simp

theorem thetaPl_lt (S X : ℕ) : thetaPl S X < 2 ^ (12 * S) := by
  unfold thetaPl
  refine xorLoop_lt (fun n => Nat.land (repP S 12 (plane S n X))
    (Nat.xor (constP S (packBetaT n) (ones S)) (thetaInner S X n))) (fun n => ?_) 12
  exact Nat.lt_of_le_of_lt Nat.and_le_left (planeLoop_lt (n := 12) (fun _ => plane S n X)
    (fun k => Nat.mul k S) (fun _ => rfl) (fun _ _ => plane_lt' S n X))

@[expose] noncomputable def quadInner (S BT X i : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j acc2 => Nat.xor acc2
    (selB (Nat.land (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt i j))
      (bitN BT (Nat.add (Nat.mul 12 i) j))) (plane S j X))) 12

theorem testBit_quadPl {S BT X p x : ℕ} (hp : p < S) (hX : Holds 12 S X p x) :
    (quadPl S BT X).testBit p = xorSum (fun i => xorSum (fun j =>
      decide (i < j) && x.testBit i && x.testBit j && BT.testBit (12 * i + j)) 12) 12 := by
  unfold quadPl
  refine (testBit_xorLoop (fun i => Nat.land (plane S i X) (quadInner S BT X i)) p 12).trans ?_
  refine xorSum_congr fun i hi => ?_
  change (plane S i X &&& quadInner S BT X i).testBit p = _
  unfold quadInner
  rw [Nat.testBit_and, testBit_plane' hp, hX i hi, testBit_xorLoop (fun j => selB (Nat.land
    (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt i j)) (bitN BT (Nat.add (Nat.mul 12 i) j)))
      (plane S j X)), and_xorSum]
  refine xorSum_congr fun j hj => ?_
  rw [blt_toNat, bitN_eq_toNat, Benes.nland, ← Trace6091.toNat_and, testBit_selB_toNat,
    testBit_plane' hp, hX j hj]
  cases decide (i < j) <;> cases x.testBit i <;> cases x.testBit j <;> simp

theorem quadPl_lt (S BT X : ℕ) : quadPl S BT X < 2 ^ S := by
  unfold quadPl
  refine xorLoop_lt (fun i => Nat.land (plane S i X) (quadInner S BT X i)) (fun i => ?_) 12
  exact Nat.lt_of_le_of_lt Nat.and_le_left (plane_lt' S i X)

theorem testBit_mux {S m x y p : ℕ} (hp : p < S) :
    (mux S m x y).testBit p = if m.testBit p then x.testBit p else y.testBit p := by
  change ((m &&& x) ||| ((ones S ^^^ m) &&& y)).testBit p = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, testBit_ones,
    decide_eq_true hp]
  cases m.testBit p <;> simp

theorem mux_lt {S m x y : ℕ} (hm : m < 2 ^ S) : mux S m x y < 2 ^ S := by
  change (m &&& x) ||| ((ones S ^^^ m) &&& y) < _
  exact Nat.or_lt_two_pow (Nat.lt_of_le_of_lt Nat.and_le_left hm)
    (Nat.lt_of_le_of_lt Nat.and_le_left (Nat.xor_lt_two_pow (ones_lt S) hm))

theorem testBit_muxLoop {S n m : ℕ} (hm : m < 2 ^ S) (sel idp : ℕ → ℕ) {b p : ℕ} (hb : b < n)
    (hp : p < S) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc (Nat.shiftLeft (mux S m (sel b) (idp b))
      (Nat.mul b S))) n).testBit (b * S + p) =
      if m.testBit p then (sel b).testBit p else (idp b).testBit p := by
  rw [testBit_planeLoop (fun b => mux S m (sel b) (idp b)) (fun b => Nat.mul b S) (fun _ => rfl)
    (fun _ _ => mux_lt hm) hb hp, testBit_mux hp]

theorem testBit_eq5 {K o v p : ℕ} (hoK : o + 5 ≤ K) (hv : v < 32) (hp : p < 2 ^ K) :
    (eq5 (2 ^ K) o v).testBit p = decide ((p >>> o) % 32 = v) := by
  have hstep : ∀ n ≤ 5, (Nat.rec (motive := fun _ => ℕ) (ones (2 ^ K)) (fun t acc => Nat.land acc
      (Bool.rec (motive := fun _ => ℕ) (clr (2 ^ K) (Nat.add o t)) (idPlane (2 ^ K) (Nat.add o t))
        (Nat.beq (bitN v t) 1))) n).testBit p = decide (∀ t < n, p.testBit (o + t) = v.testBit t) := by
    intro n
    induction n with
    | zero =>
      intro _
      change (ones (2 ^ K)).testBit p = _
      rw [testBit_ones, decide_eq_true hp]
      simp
    | succ n ih =>
      intro hn
      change (Nat.rec (motive := fun _ => ℕ) (ones (2 ^ K)) (fun t acc => Nat.land acc
        (Bool.rec (motive := fun _ => ℕ) (clr (2 ^ K) (Nat.add o t)) (idPlane (2 ^ K) (Nat.add o t))
          (Nat.beq (bitN v t) 1))) n &&& _).testBit p = _
      rw [Nat.testBit_and, ih (by omega), bitN_eq_toNat]
      have hb : o + n < K := by omega
      have e : (Bool.rec (motive := fun _ => ℕ) (clr (2 ^ K) (Nat.add o n)) (idPlane (2 ^ K) (Nat.add o n))
          (Nat.beq (v.testBit n).toNat 1)).testBit p = (p.testBit (o + n) == v.testBit n) := by
        cases hv' : v.testBit n
        · change (ones (2 ^ K) ^^^ idPlane (2 ^ K) (o + n)).testBit p = _
          rw [Nat.testBit_xor, testBit_ones, Benes.idPlane_testBit hb, decide_eq_true hp]
          cases p.testBit (o + n) <;> rfl
        · change (idPlane (2 ^ K) (o + n)).testBit p = _
          rw [Benes.idPlane_testBit hb, decide_eq_true hp]
          cases p.testBit (o + n) <;> rfl
      rw [e]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ t ht
        rcases Nat.lt_or_ge t n with h | h
        · exact h1 t h
        · rw [show t = n by omega]; exact h2
      · intro h
        exact ⟨fun t ht => h t (by omega), h n (by omega)⟩
  unfold eq5
  refine (hstep 5 le_rfl).trans ?_
  congr 1
  apply propext
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro t
    rw [(by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    by_cases ht : t < 5
    · rw [decide_eq_true ht, Bool.true_and, h t ht]
    · rw [decide_eq_false ht, Bool.false_and,
        Nat.testBit_lt_two_pow (Benes.lt_two_pow_mono (show v < 2 ^ 5 from hv) (by omega))]
  · intro h t ht
    rw [← h, (by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      decide_eq_true ht, Bool.true_and]

theorem andLoop_le (z : ℕ) (g : ℕ → ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) z (fun t acc => Nat.land acc (g t)) n ≤ z
  | 0 => le_rfl
  | n + 1 => Nat.le_trans Nat.and_le_left (andLoop_le z g n)

theorem eq5_lt (S o v : ℕ) : eq5 S o v < 2 ^ S := by
  unfold eq5
  exact Nat.lt_of_le_of_lt (andLoop_le (ones S) (fun t => Bool.rec (motive := fun _ => ℕ)
    (clr S (Nat.add o t)) (idPlane S (Nat.add o t)) (Nat.beq (bitN v t) 1)) 5) (ones_lt _)

theorem pe_lt (P c : ℕ) : pe P c < 2 ^ 5 := by
  change (P >>> (5 * c)) &&& 31 < _
  exact Nat.and_lt_two_pow _ (by decide)

theorem testBit_lookP {K o P p b : ℕ} (hoK : o + 5 ≤ K) (hp : p < 2 ^ K) (hb : b < 5) :
    (lookP (2 ^ K) o P).testBit (b * 2 ^ K + p) =
      (decide ((p >>> o) % 32 < 24) && (pe P ((p >>> o) % 32)).testBit b) := by
  unfold lookP
  refine (testBit_xorLoop (fun c => Nat.rec (motive := fun _ => ℕ) 0 (fun b acc2 => Nat.lor acc2
      (Nat.shiftLeft (selB (bitN (pe P c) b) (eq5 (2 ^ K) o c)) (Nat.mul b (2 ^ K)))) 5)
    (b * 2 ^ K + p) 24).trans ?_
  rw [xorSum_congr (g := fun c => decide (c = (p >>> o) % 32) && (pe P c).testBit b) fun c hc => ?_]
  · exact xorSum_single _ _ 24
  · rw [testBit_planeLoop (n := 5) (fun b => selB (bitN (pe P c) b) (eq5 (2 ^ K) o c))
      (fun b => Nat.mul b (2 ^ K))
      (fun _ => rfl) (fun b _ => by rw [bitN_eq_toNat]; exact selB_toNat_lt (eq5_lt _ _ _)) hb hp]
    rw [testBit_selB_bitN, testBit_eq5 hoK (by omega) hp, Bool.and_comm]
    by_cases h : (p >>> o) % 32 = c
    · simp [h]
    · simp [h, Ne.symm h]

theorem testBit_lookP' {S K o P p b : ℕ} (hS : S = 2 ^ K) (hoK : o + 5 ≤ K) (hp : p < S) (hb : b < 5) :
    (lookP S o P).testBit (b * S + p) =
      (decide ((p >>> o) % 32 < 24) && (pe P ((p >>> o) % 32)).testBit b) := by
  subst hS
  exact testBit_lookP hoK hp hb

theorem holds_net {S k n N L T : ℕ} (hS : S = 2 ^ k) (hN : netOK k N = true) (h : netP S k n N L = T)
    {u r : ℕ} (hu : u < n) (hr : r < S) :
    T.testBit (u * S + r) = L.testBit (u * S + Benes.benesPerm k N r) := by
  rw [← h, Nat.mul_comm u S, (Benes.testBit_netP hS hN L).1 u hu r hr]

theorem testBit_idP {k b p : ℕ} (hb : b < k) (hp : p < 2 ^ k) :
    (idP k).testBit (b * 2 ^ k + p) = p.testBit b := by
  unfold idP
  refine (testBit_planeLoop (S := 2 ^ k) (n := k) (fun b => idPlane (Nat.shiftLeft 1 k) b)
    (fun b => Nat.mul b (Nat.shiftLeft 1 k))
    (fun b => by rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]; rfl)
    (fun b hb => by rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]; exact idPlane_lt' hb) hb hp).trans ?_
  rw [Nat.shiftLeft_eq', Nat.one_shiftLeft, Benes.idPlane_testBit hb, decide_eq_true hp, Bool.true_and]

theorem inj_of_surj {n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < n) (hs : ∀ j < n, ∃ i < n, f i = j) :
    ∀ i < n, ∀ i' < n, f i = f i' → i = i' := by
  intro i hi i' hi' e
  have := Finset.injOn_of_surjOn_of_card_le f (s := Finset.range n) (t := Finset.range n)
    (fun x hx => by simpa using hf x (by simpa using hx))
    (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hs y (by simpa using hy)
      exact ⟨x, by simpa using hx, rfl⟩) le_rfl
  exact this (by simpa using hi) (by simpa using hi') e

theorem surj_of_inj {n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < n)
    (hi : ∀ i < n, ∀ i' < n, f i = f i' → i = i') : ∀ j < n, ∃ i < n, f i = j := by
  intro j hj
  have := Finset.surjOn_of_injOn_of_card_le f (s := Finset.range n) (t := Finset.range n)
    (fun x hx => by simpa using hf x (by simpa using hx))
    (fun x hx y hy e => hi x (by simpa using hx) y (by simpa using hy) e) le_rfl
    (by simpa using hj : j ∈ (Finset.range n : Set ℕ))
  obtain ⟨x, hx, e⟩ := this
  exact ⟨x, by simpa using hx, e⟩

theorem arrList_eq (arr : Array ℕ) : arrList arr = arr.toList := by
  cases arr
  rfl

theorem listPack_cons (x : ℕ) (l : List ℕ) :
    listPack (x :: l) = (x + ((listPack l).1 <<< 5), (listPack l).2.1 + 1,
      andB (Nat.blt x 24) (listPack l).2.2) := rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem pe_eq (P i : ℕ) : pe P i = (P >>> (5 * i)) % 32 := by
  change (P >>> (5 * i)) &&& 31 = _
  rw [(by rfl : (31 : ℕ) = 2 ^ 5 - 1), Nat.and_two_pow_sub_one_eq_mod]

theorem listPack_spec : ∀ l : List ℕ, (listPack l).2.1 = l.length ∧
    ((listPack l).2.2 = true → (∀ i < l.length, l[i]! < 24) ∧
      ∀ i < l.length, pe (listPack l).1 i = l[i]!)
  | [] => ⟨rfl, fun _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩
  | x :: l => by
    obtain ⟨ih1, ih2⟩ := listPack_spec l
    rw [listPack_cons]
    refine ⟨by simp [ih1], fun h => ?_⟩
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨ih3, ih4⟩ := ih2 h.2
    have hx := h.1
    have key : ∀ i, (x + ((listPack l).1 <<< 5)) >>> (5 * (i + 1)) = (listPack l).1 >>> (5 * i) := by
      intro i
      rw [Nat.mul_succ, Nat.add_comm (5 * i), Nat.shiftRight_add]
      congr 1
      rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (by decide),
        Nat.div_eq_of_lt (by simp only [Nat.reducePow]; omega), Nat.zero_add]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases i with _ | i
      · simpa using hx
      · simpa using ih3 i (by simpa using hi)
    · rcases i with _ | i
      · rw [pe_eq, Nat.mul_zero, Nat.shiftRight_zero, Nat.shiftLeft_eq, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega)]
        simp
      · rw [pe_eq, key, ← pe_eq, ih4 i (by simpa using hi)]
        simp

theorem permInv_get {arr : Array ℕ} (hs : ∀ j < 24, ∃ i < 24, arr[i]! = j) {j : ℕ} (hj : j < 24) :
    (Native.permInv arr)[j]! < 24 ∧ arr[(Native.permInv arr)[j]!]! = j := by
  unfold Native.permInv
  rw [getElem!_pos (Array.ofFn _) j (by simpa using hj), Array.getElem_ofFn]
  dsimp only
  cases hf : (List.range 24).find? (fun k => arr[k]! == j) with
  | none =>
    obtain ⟨i, hi, e⟩ := hs j hj
    rw [List.find?_eq_none] at hf
    exact absurd (by simpa using e) (hf i (List.mem_range.2 hi))
  | some k =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    simp only [Option.getD_some]
    exact ⟨List.mem_range.1 h2, by simpa using h1⟩

structure ArrOK (arr : Array ℕ) (P : ℕ) : Prop where
  pe : ∀ i < 24, pe P i = arr[i]!
  lt : ∀ i < 24, arr[i]! < 24
  surj : ∀ j < 24, ∃ i < 24, arr[i]! = j
  inj : ∀ i < 24, ∀ i' < 24, arr[i]! = arr[i']! → i = i'

theorem ArrOK.inv_lt {arr : Array ℕ} {P : ℕ} (h : ArrOK arr P) {j : ℕ} (hj : j < 24) :
    (Native.permInv arr)[j]! < 24 := (permInv_get h.surj hj).1

theorem ArrOK.arr_inv {arr : Array ℕ} {P : ℕ} (h : ArrOK arr P) {j : ℕ} (hj : j < 24) :
    arr[(Native.permInv arr)[j]!]! = j := (permInv_get h.surj hj).2

theorem ArrOK.inv_arr {arr : Array ℕ} {P : ℕ} (h : ArrOK arr P) {i : ℕ} (hi : i < 24) :
    (Native.permInv arr)[arr[i]!]! = i :=
  h.inj _ (h.inv_lt (h.lt i hi)) i hi (h.arr_inv (h.lt i hi))

theorem pe_invP {arr : Array ℕ} {P : ℕ} (h : ArrOK arr P) {j : ℕ} (hj : j < 24) :
    pe (invP P) j = (Native.permInv arr)[j]! := by
  rw [pe_eq]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [(by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hb : b < 5
  · rw [decide_eq_true hb, Bool.true_and]
    unfold invP
    refine (testBit_orLoop' (fun i => Nat.shiftLeft i (Nat.mul 5 (pe P i))) _ 24).trans ?_
    have hiff : (∃ k < 24, (Nat.shiftLeft k (Nat.mul 5 (pe P k))).testBit (5 * j + b) = true) ↔
        (Native.permInv arr)[j]!.testBit b = true := by
      constructor
      · rintro ⟨k, hk, hb'⟩
        change (k <<< (5 * pe P k)).testBit (5 * j + b) = true at hb'
        rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff] at hb'
        have hk32 : k < 2 ^ 5 := by simp only [Nat.reducePow]; omega
        have hpk : pe P k = j := by
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hl | hl
          · have := Nat.testBit_lt_two_pow (Benes.lt_two_pow_mono hk32
              (show 5 ≤ 5 * j + b - 5 * pe P k by omega))
            rw [this] at hb'
            exact absurd hb'.2 Bool.false_ne_true
          · omega
        have e : 5 * j + b - 5 * pe P k = b := by rw [hpk]; omega
        rw [e] at hb'
        rw [h.pe k hk] at hpk
        have := h.inv_arr hk
        rw [hpk] at this
        rw [this]
        exact hb'.2
      · intro hb'
        refine ⟨_, h.inv_lt hj, ?_⟩
        change ((Native.permInv arr)[j]! <<< (5 * pe P (Native.permInv arr)[j]!)).testBit (5 * j + b) = true
        rw [Nat.testBit_shiftLeft, h.pe _ (h.inv_lt hj), h.arr_inv hj]
        simp only [Bool.and_eq_true, decide_eq_true_iff]
        exact ⟨by omega, by rwa [show 5 * j + b - 5 * j = b by omega]⟩
    exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff]; exact hiff)
  · rw [decide_eq_false hb, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (h.inv_lt hj)
      (by calc (24 : ℕ) ≤ 2 ^ 5 := by decide
            _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)))).symm

theorem recAll_andB (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    change andB (f n) (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge i n with hl | hl
    · exact recAll_andB f n h.2 i hl
    · rw [show i = n by omega]
      exact h.1

theorem codeOK_spec {arr : Array ℕ} {P : ℕ} (hP : ∀ i < 24, pe P i = arr[i]!) (h : codeOK P = true) :
    ∀ i < 12, wordN (coeffN (permWordN arr (bmaskN i))) = permWordN arr (bmaskN i) := by
  intro i hi
  unfold codeOK at h
  have := recAll_andB (fun i => Nat.beq (wordT (coeffT (permWordT P (bmT i))))
    (permWordT P (bmT i))) (nat_lit 12) h i hi
  rw [Nat.beq_eq, Trace6091.wordT_eq, Trace6091.coeffT_eq, Trace6091.permWordT_eq hP,
    Trace6091.bmT_eq i hi, ← CFSG.Monster.B.Rep4371.native_wordN,
    ← CFSG.Monster.B.Rep4371.native_coeffN, ← CFSG.Monster.B.Rep4371.native_permWordN,
    ← CFSG.Monster.B.Rep4371.native_bmaskN] at this
  exact this

theorem permValidT_sound {arr : Array ℕ} (hsz : arr.size = 24) (h : permValidT (arrList arr) = true) :
    ArrOK arr (listPack (arrList arr)).1 ∧ Native.permValid arr = true := by
  obtain ⟨hn, hok⟩ := listPack_spec (arrList arr)
  have hlen : (arrList arr).length = 24 := by rw [arrList_eq, Array.length_toList, hsz]
  have hget : ∀ i : ℕ, (arrList arr)[i]! = arr[i]! := fun i => by
    rw [arrList_eq, Array.getElem!_toList]
  unfold permValidT at h
  generalize hL : listPack (arrList arr) = L at h hn hok ⊢
  obtain ⟨P, n, ok⟩ := L
  change andB (Nat.beq n 24) (andB ok (andB (Nat.beq (Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (pe P i))) 24) 16777215)
    (andB (codeOK P) (codeOK (invP P))))) = true at h
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨-, hok', hbij, hc1, hc2⟩ := h
  obtain ⟨hlt, hpe⟩ := hok hok'
  rw [hlen] at hlt hpe
  simp only [hget] at hlt hpe
  have hsurj : ∀ j < 24, ∃ i < 24, arr[i]! = j := by
    intro j hj
    have hb : (16777215 : ℕ).testBit j = true := by
      rw [(by rfl : (16777215 : ℕ) = 2 ^ 24 - 1), Nat.testBit_two_pow_sub_one]
      simpa using hj
    rw [← hbij, testBit_orLoop' (fun i => Nat.shiftLeft 1 (pe P i)), decide_eq_true_iff] at hb
    obtain ⟨i, hi, hb⟩ := hb
    change (1 <<< pe P i).testBit j = true at hb
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff] at hb
    exact ⟨i, hi, by rw [← hpe i hi, hb]⟩
  have hA : ArrOK arr P := ⟨hpe, hlt, hsurj, inj_of_surj hlt hsurj⟩
  refine ⟨hA, ?_⟩
  have hc1' := codeOK_spec hpe hc1
  have hc2' := codeOK_spec (fun j hj => pe_invP hA hj) hc2
  unfold Native.permValid
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hsz, hlt⟩, fun j hj => hA.inv_lt hj⟩, fun j hj => hA.arr_inv hj⟩,
    fun i hi => hA.inv_arr hi⟩, fun i hi => ⟨hc1' i hi, hc2' i hi⟩⟩

theorem permCT_two_pow {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) (i : ℕ) :
    permCT P (2 ^ i) = permCN arr (2 ^ i) := by
  rw [Trace6091.permCT_eq hA.pe, ← CFSG.Monster.B.Rep4371.native_permCN]

theorem permDT_two_pow {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) (i : ℕ) :
    permDT P (2 ^ i) = permDN arr (2 ^ i) := by
  rw [Trace6091.permDT_eq hA.pe, ← CFSG.Monster.B.Rep4371.native_permDN]

theorem holds_permC {arr : Array ℕ} {P S X p x : ℕ} (hA : ArrOK arr P) (hp : p < S)
    (hX : Holds 12 S X p x) : Holds 12 S (plin S (basisImg (permCT P)) X) p (permCN arr x) := by
  have h := holds_plin (f := permCT P) hp (fun i _ => by rw [permCT_two_pow hA]; exact permCN_lt _ _) hX
  rwa [combN_congr x (m' := fun i => permCN arr (2 ^ i)) (fun i _ => permCT_two_pow hA i),
    ← permCN_lin] at h

theorem holds_permD {arr : Array ℕ} {P S X p x : ℕ} (hA : ArrOK arr P) (hp : p < S)
    (hX : Holds 12 S X p x) : Holds 12 S (plin S (basisImg (permDT P)) X) p (permDN arr x) := by
  have h := holds_plin (f := permDT P) hp (fun i _ => by rw [permDT_two_pow hA]; exact permDN_lt _ _) hX
  rwa [combN_congr x (m' := fun i => permDN arr (2 ^ i)) (fun i _ => permDT_two_pow hA i),
    ← permDN_lin] at h

theorem quad_kappa {arr : Array ℕ} {P S X p x : ℕ} (hA : ArrOK arr P) (hp : p < S)
    (hX : Holds 12 S X p x) : (quadPl S (betaTabT P) X).testBit p = kappaN arr x := by
  rw [testBit_quadPl hp hX]
  unfold kappaN
  exact xorSum_congr fun i hi => xorSum_congr fun j hj => by
    rw [Trace6091.testBit_betaTabT hA.pe hi hj, ← CFSG.Monster.B.Rep4371.native_betaPN]

theorem permCN_zero (p : Array ℕ) : permCN p 0 = 0 := by rw [permCN_lin, combN_zero]

theorem permDN_zero (p : Array ℕ) : permDN p 0 = 0 := by rw [permDN_lin, combN_zero]

@[expose] def imgK (arr : Array ℕ) (k : ℕ × ℕ) : ℕ × ℕ :=
  (permCN arr k.1, thetaN (permCN arr k.1) ^^^ permDN arr (thetaN k.1 ^^^ k.2))

theorem imgK_lt (arr : Array ℕ) (k : ℕ × ℕ) : (imgK arr k).1 < 4096 ∧ (imgK arr k).2 < 4096 :=
  ⟨permCN_lt _ _, Nat.xor_lt_two_pow (n := 12) (thetaN_lt _) (permDN_lt _ _)⟩

theorem holds_labX {F : Fix} {arr : Array ℕ} {P x a d : ℕ} (hA : ArrOK arr P) (hx : x < SX)
    (ha : Holds 12 SX F.keyA x a) (hd : Holds 12 SX F.keyD x d) :
    Holds 12 SX (plin SX (basisImg (permCT P)) F.keyA) x (imgK arr (a, d)).1 ∧
      Holds 12 SX (Nat.xor (thetaPl SX (plin SX (basisImg (permCT P)) F.keyA))
        (plin SX (basisImg (permDT P)) (Nat.xor (thetaPl SX F.keyA) F.keyD))) x (imgK arr (a, d)).2 :=
  ⟨holds_permC hA hx ha, holds_xor (holds_thetaPl hx (holds_permC hA hx ha))
    (holds_permD hA hx (holds_xor (holds_thetaPl hx ha) hd))⟩

@[expose] noncomputable def apX (F : Fix) (P : ℕ) : ℕ := plin SX (basisImg (permCT P)) F.keyA

@[expose] noncomputable def ddX (F : Fix) (P : ℕ) : ℕ :=
  Nat.xor (thetaPl SX (apX F P)) (plin SX (basisImg (permDT P)) (Nat.xor (thetaPl SX F.keyA) F.keyD))

@[expose] noncomputable def labX (F : Fix) (P : ℕ) : ℕ :=
  Nat.lor (apX F P) (Nat.shiftLeft (ddX F P) (Nat.mul (nat_lit 12) SX))

@[expose] noncomputable def keysX (F : Fix) : ℕ :=
  Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul (nat_lit 12) SX))

theorem permXOK_eq (F : Fix) (P netX sgnX : ℕ) : permXOK F P netX sgnX =
    andB (netOK (nat_lit 17) netX) (andB (Nat.beq (netP SX (nat_lit 17) (nat_lit 24) netX (labX F P))
      (keysX F)) (Nat.beq sgnX (quadPl SX (betaTabT P) F.keyA))) := rfl

theorem testBit_keysX {F : Fix} (hK : KeyBind F) {y u : ℕ} (hy : y < SX) :
    (keysX F).testBit (u * SX + y) =
      if u < 12 then F.keyA.testBit (u * SX + y) else F.keyD.testBit ((u - 12) * SX + y) :=
  testBit_split12 hK.la hy

theorem testBit_labX (F : Fix) (P : ℕ) {y u : ℕ} (hy : y < SX) :
    (labX F P).testBit (u * SX + y) =
      if u < 12 then (apX F P).testBit (u * SX + y) else (ddX F P).testBit ((u - 12) * SX + y) :=
  testBit_split12 (plin_lt _ _ _) hy

@[expose] noncomputable def pcW (P : ℕ) : ℕ := plin SX (basisImg (permCT P)) rowCodeP

@[expose] noncomputable def k63W (P : ℕ) : ℕ := kappaT (betaTabT P) (nat_lit 63)

@[expose] noncomputable def lowPW (P : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft
      (Bool.rec (motive := fun _ => Nat) (plane SX k (pcW P)) (Nat.xor (plane SX k (pcW P))
        (plane SX (nat_lit 0) (pcW P))) (andB (Nat.blt (nat_lit 0) k) (Nat.blt k (nat_lit 6))))
      (Nat.mul k SX))) (nat_lit 12)

@[expose] noncomputable def etaW (P : ℕ) : ℕ := Nat.xor (idPlane SX (nat_lit 16)) (selB (k63W P) (ones SX))

@[expose] noncomputable def sgW (P : ℕ) : ℕ :=
  Nat.xor (quadPl SX (betaTabT P) rowCodeP) (Nat.land (etaW P) (plane SX (nat_lit 0) (pcW P)))

@[expose] noncomputable def selW (P b : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (etaW P) (plane SX (Nat.sub b (nat_lit 4)) (lowPW P))
      (Nat.blt b (nat_lit 16)))
    (plane SX b (lookP SX (nat_lit 0) P)) (Nat.blt b (nat_lit 5))

@[expose] noncomputable def labW (P : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft (mux SX valW (selW P b) (idPlane SX b)) (Nat.mul b SX)))
    (nat_lit 17)

theorem permWOK_eq (P netW sgnW : ℕ) : permWOK P netW sgnW =
    andB (netOK (nat_lit 17) netW) (andB (Nat.beq (netP SX (nat_lit 17) (nat_lit 17) netW (labW P))
      (idP (nat_lit 17))) (Nat.beq sgnW (Nat.land valW (sgW P)))) := rfl

@[expose] noncomputable def selA (P b : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => Nat) (plane SA (Nat.sub b (nat_lit 5)) (lookP SA (nat_lit 5) P))
    (plane SA b (lookP SA (nat_lit 0) P)) (Nat.blt b (nat_lit 5))

@[expose] noncomputable def labA (P : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft (mux SA valA (selA P b) (idPlane SA b)) (Nat.mul b SA)))
    (nat_lit 10)

theorem permAOK_eq (P netA : ℕ) : permAOK P netA =
    andB (netOK (nat_lit 10) netA) (Nat.beq (netP SA (nat_lit 10) (nat_lit 10) netA (labA P))
      (idP (nat_lit 10))) := rfl

theorem testBit_pos {r j : ℕ} (hj : j < 32) (k : ℕ) :
    (32 * r + j).testBit (k + 5) = r.testBit k := by
  have := Nat.testBit_two_pow_mul_add r (i := 5) (b := j) (by simpa using hj) (k + 5)
  simp only [Nat.reducePow] at this
  rw [this, ite_eq_right (by omega), Nat.add_sub_cancel]

theorem testBit_pos_lo {r j : ℕ} (hj : j < 32) {k : ℕ} (hk : k < 5) :
    (32 * r + j).testBit k = j.testBit k := by
  have := Nat.testBit_two_pow_mul_add r (i := 5) (b := j) (by simpa using hj) k
  simp only [Nat.reducePow] at this
  rw [this, ite_eq_left hk]

theorem two_mul_bit0 (m : ℕ) : (2 * m).testBit 0 = false := by
  rw [Nat.testBit_zero]
  simp

theorem two_mul_bit_succ (m k : ℕ) : (2 * m).testBit (k + 1) = m.testBit k := by
  rw [Nat.testBit_succ, Nat.mul_div_cancel_left _ (by decide)]

theorem idPlane_SX_lt {b : ℕ} (hb : b < 17) : idPlane SX b < 2 ^ SX :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [idPlane_SX hb, decide_eq_false (by omega), Bool.false_and]

theorem testBit_mod2048 (r : ℕ) {k : ℕ} (hk : k < 11) : (r % 2048).testBit k = r.testBit k := by
  rw [(by rfl : (2048 : ℕ) = 2 ^ 11), Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and]

theorem holds_rowCode {r j : ℕ} (hr : r < 4096) (hj : j < 32) :
    Holds 12 SX rowCodeP (32 * r + j) (2 * (r % 2048)) := fun b hb => by
  have hx : 32 * r + j < SX := by rw [SX_eq]; omega
  unfold rowCodeP
  refine (testBit_orLoop' (fun k => Nat.shiftLeft (idPlane SX (Nat.add k (nat_lit 5)))
    (Nat.mul (Nat.add k (nat_lit 1)) SX)) _ 11).trans ?_
  have e : ∀ k < 11, (Nat.shiftLeft (idPlane SX (Nat.add k (nat_lit 5)))
      (Nat.mul (Nat.add k (nat_lit 1)) SX)).testBit (b * SX + (32 * r + j)) =
      (decide (k + 1 = b) && r.testBit k) := fun k hk => by
    change (Nat.shiftLeft (idPlane SX (k + 5)) ((k + 1) * SX)).testBit (b * SX + (32 * r + j)) = _
    rw [testBit_shl_plane (idPlane_SX_lt (by omega)) hx, idPlane_SX (by omega), decide_eq_true hx,
      Bool.true_and, testBit_pos (by omega)]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    rw [e k hk, Bool.and_eq_true, decide_eq_true_iff] at h
    rw [← h.1, two_mul_bit_succ, testBit_mod2048 r hk]
    exact h.2
  · intro h
    rcases b with _ | k
    · rw [two_mul_bit0] at h
      exact absurd h Bool.false_ne_true
    · rw [two_mul_bit_succ, testBit_mod2048 r (by omega)] at h
      refine ⟨k, by omega, ?_⟩
      rw [e k (by omega), h]
      simp

theorem holds_pcW {arr : Array ℕ} {P r j : ℕ} (hA : ArrOK arr P) (hr : r < 4096) (hj : j < 32) :
    Holds 12 SX (pcW P) (32 * r + j) (permCN arr (2 * (r % 2048))) :=
  holds_permC hA (by rw [SX_eq]; omega) (holds_rowCode hr hj)

theorem testBit_pi0N (z k : ℕ) : (pi0N z).testBit k = (z.testBit k ^^ (z.testBit 0 && decide (k < 6))) := by
  unfold pi0N
  rw [Nat.testBit_xor]
  cases z.testBit 0
  · simp
  · simp only [ite_true, Bool.true_and]
    rw [(by rfl : (63 : ℕ) = 2 ^ 6 - 1), Nat.testBit_two_pow_sub_one]

theorem testBit_lowPW {P x z k : ℕ} (hx : x < SX) (hz : Holds 12 SX (pcW P) x z)
    (hk1 : 1 ≤ k) (hk : k < 12) : (lowPW P).testBit (k * SX + x) = (pi0N z).testBit k := by
  unfold lowPW
  refine (testBit_planeLoop (n := 12) (fun k => Bool.rec (motive := fun _ => Nat) (plane SX k (pcW P))
      (Nat.xor (plane SX k (pcW P)) (plane SX (nat_lit 0) (pcW P)))
      (andB (Nat.blt (nat_lit 0) k) (Nat.blt k (nat_lit 6)))) (fun k => Nat.mul k SX) (fun _ => rfl)
    (fun k _ => ?_) hk hx).trans ?_
  · dsimp only
    cases andB (Nat.blt (nat_lit 0) k) (Nat.blt k (nat_lit 6))
    · exact plane_lt' _ _ _
    · exact Nat.xor_lt_two_pow (plane_lt' _ _ _) (plane_lt' _ _ _)
  · dsimp only
    rw [testBit_pi0N]
    by_cases h6 : k < 6
    · have e : andB (Nat.blt (nat_lit 0) k) (Nat.blt k (nat_lit 6)) = true := by
        rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq]
        exact ⟨(show 0 < k by omega), h6⟩
      rw [e]
      change (Nat.xor (plane SX k (pcW P)) (plane SX 0 (pcW P))).testBit x = _
      rw [Benes.nxor, Nat.testBit_xor, testBit_plane' hx, testBit_plane' hx, hz k hk, hz 0 (by decide),
        decide_eq_true h6, Bool.and_true]
    · have e : andB (Nat.blt (nat_lit 0) k) (Nat.blt k (nat_lit 6)) = false := by
        rw [andB_eq, Bool.and_eq_false_iff]
        right
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
        exact h6
      rw [e]
      change (plane SX k (pcW P)).testBit x = _
      rw [testBit_plane' hx, hz k hk, decide_eq_false h6, Bool.and_false, Bool.xor_false]

theorem testBit_etaW {arr : Array ℕ} {P x : ℕ} (hA : ArrOK arr P) (hx : x < SX) :
    (etaW P).testBit x = (x.testBit 16 ^^ kappaN arr 63) := by
  unfold etaW k63W
  change (idPlane SX 16 ^^^ selB (kappaT (betaTabT P) 63) (ones SX)).testBit x = _
  rw [Nat.testBit_xor, idPlane_SX (by decide), decide_eq_true hx, Bool.true_and,
    Trace6091.kappaT_eq hA.pe, ← CFSG.Monster.B.Rep4371.native_kappaN, testBit_selB_toNat, testBit_ones,
    decide_eq_true hx, Bool.and_true]

theorem testBit_sgW {arr : Array ℕ} {P r j : ℕ} (hA : ArrOK arr P) (hr : r < 4096) (hj : j < 32) :
    (sgW P).testBit (32 * r + j) = (kappaN arr (2 * (r % 2048)) ^^
      ((decide (2048 ≤ r) ^^ kappaN arr 63) && (permCN arr (2 * (r % 2048))).testBit 0)) := by
  have hx : 32 * r + j < SX := by rw [SX_eq]; omega
  unfold sgW
  change (quadPl SX (betaTabT P) rowCodeP ^^^ (etaW P &&& plane SX 0 (pcW P))).testBit (32 * r + j) = _
  rw [Nat.testBit_xor, Nat.testBit_and, quad_kappa hA hx (holds_rowCode hr hj), testBit_etaW hA hx,
    testBit_plane' hx, holds_pcW hA hr hj 0 (by decide), testBit_pos (k := 11) (by omega)]
  rw [Benes.testBit_top (b := 11) (by simpa using hr)]

@[expose] def rowP (arr : Array ℕ) (r : ℕ) : ℕ :=
  2048 * (decide (2048 ≤ r) ^^ kappaN arr 63).toNat + pi0N (permCN arr (2 * (r % 2048))) / 2

theorem pi0N_lt {a : ℕ} (ha : a < 4096) : pi0N a < 4096 := by
  unfold pi0N
  have : (if a.testBit 0 = true then 63 else 0) < 2 ^ 12 := by split_ifs <;> decide
  exact Nat.xor_lt_two_pow (n := 12) ha this

theorem rowP_lt (arr : Array ℕ) (r : ℕ) : rowP arr r < 4096 := by
  have := pi0N_lt (permCN_lt arr (2 * (r % 2048)))
  unfold rowP
  cases decide (2048 ≤ r) ^^ kappaN arr 63 <;> simp <;> omega

theorem rowP_testBit (arr : Array ℕ) (r k : ℕ) : (rowP arr r).testBit k =
    if k < 11 then (pi0N (permCN arr (2 * (r % 2048))) / 2).testBit k
    else ((decide (2048 ≤ r) ^^ kappaN arr 63).toNat).testBit (k - 11) := by
  have hw : pi0N (permCN arr (2 * (r % 2048))) / 2 < 2 ^ 11 := by
    have := pi0N_lt (permCN_lt arr (2 * (r % 2048)))
    simp only [Nat.reducePow]
    omega
  exact Nat.testBit_two_pow_mul_add ((decide (2048 ≤ r) ^^ kappaN arr 63).toNat) hw k

@[expose] def fW (arr : Array ℕ) (x : ℕ) : ℕ :=
  if x % 32 < 24 then 32 * rowP arr (x / 32) + arr[x % 32]! else x

theorem testBit_labW {arr : Array ℕ} {P x b : ℕ} (hA : ArrOK arr P) (hx : x < SX) (hb : b < 17) :
    (labW P).testBit (b * SX + x) = (fW arr x).testBit b := by
  unfold labW
  refine (testBit_muxLoop (n := 17) valW_lt (selW P) (fun b => idPlane SX b) hb hx).trans ?_
  rw [testBit_valW]
  unfold fW
  by_cases hv : x % 32 < 24
  · rw [decide_eq_true ⟨hx, hv⟩, ite_eq_left rfl, ite_eq_left hv]
    have hr : x / 32 < 4096 := by rw [SX_eq] at hx; omega
    have hxe : x = 32 * (x / 32) + x % 32 := by omega
    have hz := holds_pcW hA hr (Nat.mod_lt x (by decide))
    rw [← hxe] at hz
    have hlt : arr[x % 32]! < 32 := by have := hA.lt _ hv; omega
    by_cases h5 : b < 5
    · have e : Nat.blt b (nat_lit 5) = true := by rw [Nat.blt_eq]; exact h5
      unfold selW
      rw [e]
      change (plane SX b (lookP SX 0 P)).testBit x = _
      rw [testBit_plane' hx, testBit_lookP' (K := 17) (o := 0) SX_eq (by decide) hx h5,
        Nat.shiftRight_zero, decide_eq_true hv, Bool.true_and, hA.pe _ hv, testBit_pos_lo hlt h5]
    · have e : Nat.blt b (nat_lit 5) = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
        exact h5
      have hRb : (32 * rowP arr (x / 32) + arr[x % 32]!).testBit b = (rowP arr (x / 32)).testBit (b - 5) := by
        rw [show b = (b - 5) + 5 by omega, testBit_pos hlt, Nat.add_sub_cancel]
      rw [hRb, rowP_testBit]
      by_cases h16 : b < 16
      · have e2 : Nat.blt b (nat_lit 16) = true := by rw [Nat.blt_eq]; exact h16
        unfold selW
        rw [e, e2]
        change (plane SX (b - 4) (lowPW P)).testBit x = _
        rw [testBit_plane' hx, testBit_lowPW hx hz (by omega) (by omega), ite_eq_left (by omega),
          (by rfl : (2 : ℕ) = 2 ^ 1), Nat.testBit_div_two_pow, show b - 5 + 1 = b - 4 by omega]
      · have e2 : Nat.blt b (nat_lit 16) = false := by
          rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
          exact h16
        unfold selW
        rw [e, e2]
        change (etaW P).testBit x = _
        rw [testBit_etaW hA hx, ite_eq_right (by omega), show b - 5 - 11 = 0 by omega, Nat.testBit_zero]
        have h16' : b = 16 := by omega
        subst h16'
        rw [hxe, testBit_pos (k := 11) (Nat.mod_lt x (by decide)), ← hxe,
          Benes.testBit_top (b := 11) (by simpa using hr)]
        cases (decide (2048 ≤ x / 32) ^^ kappaN arr 63) <;> rfl
  · rw [decide_eq_false (fun h => hv h.2), ite_eq_right (by simp), ite_eq_right hv, idPlane_SX hb, decide_eq_true hx,
      Bool.true_and]

theorem fW_lt {arr : Array ℕ} {P x : ℕ} (hA : ArrOK arr P) (hx : x < SX) : fW arr x < 2 ^ 17 := by
  unfold fW
  split_ifs with hv
  · have := rowP_lt arr (x / 32)
    have := hA.lt _ hv
    simp only [Nat.reducePow]
    omega
  · rw [← SX_eq]
    exact hx

@[expose] def fA (arr : Array ℕ) (x : ℕ) : ℕ :=
  if x % 32 < 24 ∧ x / 32 < 24 then 32 * arr[x / 32]! + arr[x % 32]! else x

theorem testBit_labA {arr : Array ℕ} {P x b : ℕ} (hA : ArrOK arr P) (hx : x < SA) (hb : b < 10) :
    (labA P).testBit (b * SA + x) = (fA arr x).testBit b := by
  unfold labA
  refine (testBit_muxLoop (n := 10) valA_lt (selA P) (fun b => idPlane SA b) hb hx).trans ?_
  rw [testBit_valA]
  unfold fA
  by_cases hv : x % 32 < 24 ∧ x / 32 < 24
  · rw [decide_eq_true ⟨hx, hv⟩, ite_eq_left rfl, ite_eq_left hv]
    have hlt : arr[x % 32]! < 32 := by have := hA.lt _ hv.1; omega
    have hlt' : arr[x / 32]! < 24 := hA.lt _ hv.2
    have hsx : x < 2 ^ 10 := hx
    by_cases h5 : b < 5
    · have e : Nat.blt b (nat_lit 5) = true := by rw [Nat.blt_eq]; exact h5
      unfold selA
      rw [e]
      change (plane SA b (lookP SA 0 P)).testBit x = _
      rw [testBit_plane' hx, testBit_lookP' (K := 10) (o := 0) SA_eq (by decide) hx h5,
        Nat.shiftRight_zero, decide_eq_true hv.1, Bool.true_and, hA.pe _ hv.1, testBit_pos_lo hlt h5]
    · have e : Nat.blt b (nat_lit 5) = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
        exact h5
      unfold selA
      rw [e]
      change (plane SA (b - 5) (lookP SA 5 P)).testBit x = _
      have hd : (x >>> 5) % 32 = x / 32 := by
        rw [Nat.shiftRight_eq_div_pow]
        simp only [Nat.reducePow]
        omega
      rw [testBit_plane' hx, testBit_lookP' (K := 10) (o := 5) SA_eq (by decide) hx (by omega), hd,
        decide_eq_true hv.2,
        Bool.true_and, hA.pe _ hv.2, show b = (b - 5) + 5 by omega, testBit_pos hlt, Nat.add_sub_cancel]
  · rw [decide_eq_false (fun h => hv h.2), ite_eq_right (by simp), ite_eq_right hv, idPlane_SA hb, decide_eq_true hx,
      Bool.true_and]

theorem fA_lt {arr : Array ℕ} {P x : ℕ} (hA : ArrOK arr P) (hx : x < SA) : fA arr x < 2 ^ 10 := by
  unfold fA
  split_ifs with hv
  · have := hA.lt _ hv.1
    have := hA.lt _ hv.2
    simp only [Nat.reducePow]
    omega
  · exact hx

theorem label_net {k N L : ℕ} {f : ℕ → ℕ} (hN : netOK k N = true) (h : netP (2 ^ k) k k N L = idP k)
    (hL : ∀ x < 2 ^ k, ∀ b < k, L.testBit (b * 2 ^ k + x) = (f x).testBit b)
    (hf : ∀ x < 2 ^ k, f x < 2 ^ k) {y : ℕ} (hy : y < 2 ^ k) : f (Benes.benesPerm k N y) = y := by
  have hv := Benes.stagesValid_of_netOK hN
  have hpy := Benes.benesPerm_lt hv hy
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < k
  · rw [← hL _ hpy b hb, ← holds_net rfl hN h hb hy, testBit_idP hb hy]
  · rw [Nat.testBit_lt_two_pow (Benes.lt_two_pow_mono (hf _ hpy) (by omega)),
      Nat.testBit_lt_two_pow (Benes.lt_two_pow_mono hy (by omega))]

theorem label_inv {k N : ℕ} {f : ℕ → ℕ} (hN : netOK k N = true)
    (hf : ∀ y < 2 ^ k, f (Benes.benesPerm k N y) = y) {x : ℕ} (hx : x < 2 ^ k) :
    f x = Benes.benesInv k N x := by
  have hv := Benes.stagesValid_of_netOK hN
  have := hf _ (Benes.benesInv_lt hv hx)
  rwa [Benes.benesPerm_benesInv hv] at this

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

theorem xT_perm {arr : Array ℕ} (hv : Native.permValid arr = true) (hG : KeysGood) {p : ℕ}
    (hp : p < 98280) :
    Native.GD.xT (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) p =
      [((Native.mkCtx ()).find (imgK arr (keyQ p)).1 (imgK arr (keyQ p)).2,
        sgnI (kappaN arr (keyQ p).1))] := by
  have hb := hG.1 p hp
  unfold Native.GD.xT
  simp only [Native.GD.ofGen]
  rw [mkCtx_keys hp, mkCtx_th, fastAct_perm hv hb.1 hb.2]
  rfl

theorem perm_resX (h2 : 2 * h = 1) {arr : Array ℕ} (hv : Native.permValid arr = true) (hG : KeysGood)
    (hcov : ∀ p < 98280, ∃ q < 98280, imgK arr (keyQ p) = keyQ q)
    (hinj : ∀ p < 98280, ∀ p' < 98280, imgK arr (keyQ p) = imgK arr (keyQ p') → p = p')
    (v : Native.DVec) {p q : ℕ} (hp : p < 98280) (hq : q < 98280) (hpq : imgK arr (keyQ p) = keyQ q) :
    resM h (Native.applyGen (Native.mkCtx ()) (.perm arr) v) (300 + q) =
      ((sgnI (kappaN arr (keyQ p).1) : ℤ) : ZMod M) * resM h v (300 + p) := by
  have hσ : ∀ p < 98280, ∀ q < 98280, imgK arr (keyQ p) = keyQ q →
      (Native.mkCtx ()).find (imgK arr (keyQ p)).1 (imgK arr (keyQ p)).2 = q :=
    fun p _ q hq e => by rw [e]; exact mkCtx_find hG hq
  have hinjσ : ∀ p1 < 98280, ∀ p2 < 98280,
      (Native.mkCtx ()).find (imgK arr (keyQ p1)).1 (imgK arr (keyQ p1)).2 =
        (Native.mkCtx ()).find (imgK arr (keyQ p2)).1 (imgK arr (keyQ p2)).2 → p1 = p2 := by
    intro p1 hp1 p2 hp2 e
    obtain ⟨q1, hq1, e1⟩ := hcov p1 hp1
    obtain ⟨q2, hq2, e2⟩ := hcov p2 hp2
    rw [hσ p1 hp1 q1 hq1 e1, hσ p2 hp2 q2 hq2 e2] at e
    subst e
    exact hinj p1 hp1 p2 hp2 (e1.trans e2.symm)
  change resM h (Native.applyGD (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.perm arr))
    v) (300 + q) = _
  rw [applyGD_resX h2 _ _ _ hq, sum_scat_single (fun p hp => xT_perm hv hG hp) hinjσ]
  have hex : ∃ p' < 98280, (Native.mkCtx ()).find (imgK arr (keyQ p')).1 (imgK arr (keyQ p')).2 = q :=
    ⟨p, hp, hσ p hp q hq hpq⟩
  rw [dite_eq_left hex]
  obtain ⟨hlt, he⟩ := hex.choose_spec
  have hc : hex.choose = p := hinjσ _ hlt p hp (he.trans (hσ p hp q hq hpq).symm)
  rw [hc]

theorem permG_get {arr : Array ℕ} {k i : ℕ} (hk : k < 24) (hi : i < 24) :
    (Native.permG arr)[k * 24 + i]! = if arr[k]! = i then 1 else 0 := by
  unfold Native.permG
  rw [getElem!_pos (Array.ofFn _) (k * 24 + i) (by simp; omega), Array.getElem_ofFn]
  have e1 : (k * 24 + i) / 24 = k := by omega
  have e2 : (k * 24 + i) % 24 = i := by omega
  simp only [e1, e2]

theorem permG_sum {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) (f : ℕ → ZMod M) {i : ℕ} (hi : i < 24) :
    ∑ k ∈ Finset.range 24, (((Native.permG arr)[k * 24 + i]! : ℤ) : ZMod M) * f k =
      f (Native.permInv arr)[i]! := by
  rw [Finset.sum_eq_single (Native.permInv arr)[i]!]
  · rw [permG_get (hA.inv_lt hi) hi, ite_eq_left (hA.arr_inv hi)]
    simp
  · intro b hb hne
    have hb' := Finset.mem_range.1 hb
    rw [permG_get hb' hi, ite_eq_right]
    · simp
    · intro e
      apply hne
      rw [← e, hA.inv_arr hb']
  · intro hn
    exact absurd (Finset.mem_range.2 (hA.inv_lt hi)) hn

theorem perm_resA (h2 : 2 * h = 1) {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) (v : Native.DVec)
    {i j : ℕ} (hi : i < 24) (hj : j < 24) :
    resM h (Native.applyGen (Native.mkCtx ()) (.perm arr) v) (Native.aIdx i j) =
      resM h v (Native.aIdx (Native.permInv arr)[i]! (Native.permInv arr)[j]!) := by
  change resM h (Native.applyGD (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.perm arr))
    v) _ = _
  rw [applyGD_resA h2 _ _ _ (InitAux.aIdx_lt i hi j hj), ListAux.aPos_aIdx i hi j hj]
  have hG : (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).G = Native.permG arr := by
    simp only [Native.GD.ofGen]
  have hl : (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).latS = 0 := by simp only [Native.GD.ofGen]
  rw [hG, hl]
  have e : ∀ k, ∑ l ∈ Finset.range 24, (((Native.permG arr)[k * 24 + min i j]! : ℤ) : ZMod M) *
      (((Native.permG arr)[l * 24 + max i j]! : ℤ) : ZMod M) * resM h v (Native.aIdx k l) =
      (((Native.permG arr)[k * 24 + min i j]! : ℤ) : ZMod M) * ∑ l ∈ Finset.range 24,
        (((Native.permG arr)[l * 24 + max i j]! : ℤ) : ZMod M) * resM h v (Native.aIdx k l) := by
    intro k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [e]
  rw [permG_sum hA _ (by omega : min i j < 24), permG_sum hA _ (by omega : max i j < 24), Nat.mul_zero,
    pow_zero, one_mul]
  rcases le_total i j with hij | hij
  · rw [min_eq_left hij, max_eq_right hij]
  · rw [min_eq_right hij, max_eq_left hij, ListAux.aIdx_comm _ (hA.inv_lt hj) _ (hA.inv_lt hi)]

theorem betaTab_get (arr : Array ℕ) {i j : ℕ} (hi : i < 12) (hj : j < 12) :
    (Native.betaTab arr)[12 * i + j]! = betaPN arr i j := by
  unfold Native.betaTab
  rw [getElem!_pos (Array.ofFn _) (12 * i + j) (by simp; omega), Array.getElem_ofFn]
  have e1 : (12 * i + j) / 12 = i := by omega
  have e2 : (12 * i + j) % 12 = j := by omega
  simp only [e1, e2]

theorem kappaT_native (arr : Array ℕ) (a : ℕ) : Native.kappaT (Native.betaTab arr) a = kappaN arr a := by
  unfold Native.kappaT kappaN
  exact xorSum_congr fun i hi => xorSum_congr fun j hj => by rw [betaTab_get arr hi hj]

theorem monoRows_get (rm : Bool → ℕ → Bool × Bool × ℕ) {r : ℕ} (hr : r < 4096) :
    (Native.monoRows rm)[r]! = [(Native.rowIdx (rm (Native.rowEta r) (Native.rowC r)).2.1
      (rm (Native.rowEta r) (Native.rowC r)).2.2, sgnI (rm (Native.rowEta r) (Native.rowC r)).1)] := by
  unfold Native.monoRows
  rw [getElem!_pos _ r (by simp; omega)]
  simp

theorem pi0N_bit0 (x : ℕ) : (pi0N x).testBit 0 = false := by
  rw [testBit_pi0N]
  cases x.testBit 0 <;> rfl

theorem pi0N_of_even {x : ℕ} (h : x.testBit 0 = false) : pi0N x = x := by
  unfold pi0N
  rw [ite_eq_right (by simp [h]), Nat.xor_zero]

@[expose] def sgP (arr : Array ℕ) (r : ℕ) : Bool :=
  (kappaN arr (2 * (r % 2048)) ^^
    ((decide (2048 ≤ r) ^^ kappaN arr 63) && (permCN arr (2 * (r % 2048))).testBit 0))

theorem ePermT_rows (arr : Array ℕ) (r : ℕ) :
    Native.rowIdx (Native.ePermT arr (Native.betaTab arr) (Native.rowEta r) (Native.rowC r)).2.1
      (Native.ePermT arr (Native.betaTab arr) (Native.rowEta r) (Native.rowC r)).2.2 = rowP arr r ∧
    (Native.ePermT arr (Native.betaTab arr) (Native.rowEta r) (Native.rowC r)).1 = sgP arr r := by
  have hc : pi0N (Native.rowC r) = 2 * (r % 2048) := pi0N_of_even (two_mul_bit0 _)
  unfold Native.ePermT
  simp only [kappaT_native, hc, Native.rowEta]
  refine ⟨?_, rfl⟩
  unfold Native.rowIdx rowP
  rw [pi0N_of_even (pi0N_bit0 _)]
  have := pi0N_lt (permCN_lt arr (2 * (r % 2048)))
  rw [Nat.mod_eq_of_lt (by omega)]
  cases decide (2048 ≤ r) ^^ kappaN arr 63 <;> simp

theorem wT_perm (arr : Array ℕ) {p : ℕ} (hp : p < 98304) :
    (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).wT p =
      [(rowP arr (p / 24) * 24 + p % 24, sgnI (sgP arr (p / 24)))] := by
  unfold Native.GD.wT
  simp only [Native.GD.ofGen]
  rw [monoRows_get _ (by omega), (ePermT_rows arr _).1, (ePermT_rows arr _).2]
  rfl

theorem xor_inj' {x y T : ℕ} (e : x ^^^ T = y ^^^ T) : x = y := by
  have := congrArg (· ^^^ T) e
  simpa [Nat.xor_assoc] using this

theorem perm_resW (h2 : 2 * h = 1) {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P)
    (hRinj : ∀ r < 4096, ∀ r' < 4096, rowP arr r = rowP arr r' → r = r') (v : Native.DVec)
    {r j : ℕ} (hr : r < 4096) (hj : j < 24) :
    resM h (Native.applyGen (Native.mkCtx ()) (.perm arr) v) (98580 + 24 * rowP arr r + j) =
      ((sgnI (sgP arr r) : ℤ) : ZMod M) * resM h v (98580 + 24 * r + (Native.permInv arr)[j]!) := by
  have hR := rowP_lt arr r
  change resM h (Native.applyGD (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.perm arr))
    v) _ = _
  rw [Nat.add_assoc, applyGD_resW h2 _ _ _ (by omega)]
  have hinj : ∀ p < 98304, ∀ p' < 98304, rowP arr (p / 24) * 24 + p % 24 =
      rowP arr (p' / 24) * 24 + p' % 24 → p = p' := by
    intro p hp p' hp' e
    have h1 : p % 24 = p' % 24 := by omega
    have h2 : rowP arr (p / 24) = rowP arr (p' / 24) := by omega
    have := hRinj _ (by omega) _ (by omega) h2
    omega
  rw [sum_scat_single (σ := fun p => rowP arr (p / 24) * 24 + p % 24) (fun p hp => wT_perm arr hp) hinj]
  have hex : ∃ p < 98304, rowP arr (p / 24) * 24 + p % 24 = 24 * rowP arr r + j :=
    ⟨24 * r + j, by omega, by
      rw [show (24 * r + j) / 24 = r by omega, show (24 * r + j) % 24 = j by omega]
      ring⟩
  rw [dite_eq_left hex]
  obtain ⟨hlt, he⟩ := hex.choose_spec
  have hc : hex.choose = 24 * r + j := hinj _ hlt _ (by omega) (by
    rw [he, show (24 * r + j) / 24 = r by omega, show (24 * r + j) % 24 = j by omega]
    ring)
  rw [hc, show (24 * r + j) / 24 = r by omega, show (24 * r + j) % 24 = j by omega]
  have hG : (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).G = Native.permG arr := by
    simp only [Native.GD.ofGen]
  have hl : (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).latS = 0 := by simp only [Native.GD.ofGen]
  have hr0 : (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).rowS = 0 := by simp only [Native.GD.ofGen]
  rewrite [hG, hl, hr0, Nat.add_zero, pow_zero, one_mul, permG_sum hA _ hj, Nat.mul_comm r 24]
  rfl

end PermAux

open PermAux

theorem perm15_sound {F : Fix} {T : Tab} (hK : KeyBind F) (hG : KeysGood) {arr : Array ℕ}
    (hsz : arr.size = 24) {k : ℕ} (he : entryOK F T (arrList arr) k = true) {v : Native.DVec}
    {t : St} (ht : RepN 4 v t) (f : Bool) :
    Native.permValid arr = true ∧
      RepN 4 (Native.applyGen (Native.mkCtx ()) (.perm arr) v) (f, permStep T k t.2.1 t.2.2.1 t.2.2.2) := by
  unfold entryOK at he
  rw [andB_eq, Bool.and_eq_true] at he
  obtain ⟨hA, hv⟩ := permValidT_sound hsz he.1
  refine ⟨hv, ?_⟩
  have he2 := he.2
  generalize listPack (arrList arr) = L at hA he2
  obtain ⟨P, rest⟩ := L
  change ArrOK arr P at hA
  change andB (permXOK F P (T.netX k) (T.sgnX k))
    (andB (permWOK P (T.netW k) (T.sgnW k)) (permAOK P (T.netA k))) = true at he2
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, permXOK_eq, permWOK_eq, permAOK_eq,
    andB_eq, andB_eq, andB_eq, andB_eq, andB_eq] at he2
  simp only [Bool.and_eq_true, Nat.beq_eq] at he2
  obtain ⟨⟨hXn, hXl, hXs⟩, ⟨hWn, hWl, hWs⟩, ⟨hAn, hAl⟩⟩ := he2
  obtain ⟨hX1, hX2, hX3, hA1, hA2, hA3, hW1, hW2, hW3⟩ := ht
  have h2 := two_hN (np := 4) (by decide)
  have hSX : SX = 131072 := rfl
  have hSA : SA = 1024 := rfl
  have hvX := Benes.stagesValid_of_netOK hXn
  have hvW := Benes.stagesValid_of_netOK hWn
  have hvA := Benes.stagesValid_of_netOK hAn
  have hπX : ∀ y < SX, Benes.benesPerm 17 (T.netX k) y < SX := fun y hy => Benes.benesPerm_lt hvX hy
  have hπW : ∀ y < SX, Benes.benesPerm 17 (T.netW k) y < SX := fun y hy => Benes.benesPerm_lt hvW hy
  have hπA : ∀ y < SA, Benes.benesPerm 10 (T.netA k) y < SA := fun y hy => Benes.benesPerm_lt hvA hy
  have hπXi : ∀ y y', Benes.benesPerm 17 (T.netX k) y = Benes.benesPerm 17 (T.netX k) y' → y = y' :=
    fun y y' e => by
      rw [← Benes.benesInv_benesPerm hvX y, e, Benes.benesInv_benesPerm hvX y']
  have htr : ∀ y < SX, ∀ b < 12,
      F.keyA.testBit (b * SX + y) = (apX F P).testBit (b * SX + Benes.benesPerm 17 (T.netX k) y) ∧
      F.keyD.testBit (b * SX + y) = (ddX F P).testBit (b * SX + Benes.benesPerm 17 (T.netX k) y) := by
    intro y hy b hb
    have e1 := holds_net (n := 24) SX_eq hXn hXl (u := b) (by omega) hy
    have e2 := holds_net (n := 24) SX_eq hXn hXl (u := b + 12) (by omega) hy
    rw [testBit_keysX hK hy, testBit_labX F P (hπX y hy), ite_eq_left hb, ite_eq_left hb] at e1
    rw [testBit_keysX hK hy, testBit_labX F P (hπX y hy), ite_eq_right (by omega), ite_eq_right (by omega),
      Nat.add_sub_cancel] at e2
    exact ⟨e1, e2⟩
  have hkeyS0 : ∀ q < 98280, ∃ p < 98280, Benes.benesPerm 17 (T.netX k) (xposK q) = xposK p ∧
      imgK arr (keyQ p) = keyQ q := by
    intro q hq
    have hy := InitAux.xposK_lt' hq
    have hx := hπX _ hy
    have ha1 : Holds 12 SX (apX F P) (Benes.benesPerm 17 (T.netX k) (xposK q)) (keyQ q).1 :=
      fun b hb => by rw [← (htr _ hy b hb).1, hK.ka q hq b hb]
    have hd1 : Holds 12 SX (ddX F P) (Benes.benesPerm 17 (T.netX k) (xposK q)) (keyQ q).2 :=
      fun b hb => by rw [← (htr _ hy b hb).2, hK.kd q hq b hb]
    by_cases hkey : ∃ p < 98280, xposK p = Benes.benesPerm 17 (T.netX k) (xposK q)
    · obtain ⟨p, hp, e⟩ := hkey
      have hl := holds_labX (F := F) hA hx (a := (keyQ p).1) (d := (keyQ p).2)
        (fun b hb => by rw [← e]; exact hK.ka p hp b hb) (fun b hb => by rw [← e]; exact hK.kd p hp b hb)
      refine ⟨p, hp, e.symm, Prod.ext ?_ ?_⟩
      · exact holds_eq hl.1 ha1 (imgK_lt arr _).1 (hG.1 q hq).1
      · exact holds_eq hl.2 hd1 (imgK_lt arr _).2 (hG.1 q hq).2
    · exfalso
      have hnk : ∀ p < 98280, xposK p ≠ Benes.benesPerm 17 (T.netX k) (xposK q) :=
        fun p hp e => hkey ⟨p, hp, e⟩
      have hl := holds_labX (F := F) hA hx (a := 0) (d := 0)
        (fun b hb => by rw [hK.pa _ hx hnk b hb, Nat.zero_testBit])
        (fun b hb => by rw [hK.pd _ hx hnk b hb, Nat.zero_testBit])
      have hz : imgK arr (0, 0) = (0, 0) := by
        unfold imgK
        rw [permCN_zero, thetaN_zero, Nat.xor_zero, permDN_zero, Nat.xor_zero]
      rw [hz] at hl
      apply keyQ_ne_zero hq
      exact Prod.ext (holds_eq ha1 hl.1 (hG.1 q hq).1 (by decide))
        (holds_eq hd1 hl.2 (hG.1 q hq).2 (by decide))
  have hkeyS1 : ∀ q, ∃ p, q < 98280 → p < 98280 ∧ Benes.benesPerm 17 (T.netX k) (xposK q) = xposK p ∧
      imgK arr (keyQ p) = keyQ q := fun q => by
    by_cases hq : q < 98280
    · obtain ⟨p, hp, e, i⟩ := hkeyS0 q hq
      exact ⟨p, fun _ => ⟨hp, e, i⟩⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose ρ hρ using hkeyS1
  have hkeyS : ∀ q < 98280, ∃ p < 98280, Benes.benesPerm 17 (T.netX k) (xposK q) = xposK p ∧
      imgK arr (keyQ p) = keyQ q := fun q hq => ⟨ρ q, hρ q hq⟩
  have hcovπ : ∀ p < 98280, ∃ q < 98280, Benes.benesPerm 17 (T.netX k) (xposK q) = xposK p := by
    intro p hp
    obtain ⟨q, hq, e⟩ := surj_of_inj (f := ρ) (fun q hq => (hρ q hq).1)
      (fun q hq q' hq' e => InitAux.xposK_inj hq hq'
        (hπXi _ _ (by rw [(hρ q hq).2.1, (hρ q' hq').2.1, e]))) p hp
    exact ⟨q, hq, by rw [(hρ q hq).2.1, e]⟩
  have hcov : ∀ p < 98280, ∃ q < 98280, imgK arr (keyQ p) = keyQ q ∧
      Benes.benesPerm 17 (T.netX k) (xposK q) = xposK p := by
    intro p hp
    obtain ⟨q, hq, e⟩ := hcovπ p hp
    obtain ⟨p', hp', e', hi⟩ := hkeyS q hq
    have : p' = p := InitAux.xposK_inj hp' hp (e'.symm.trans e)
    subst this
    exact ⟨q, hq, hi, e⟩
  have hinj : ∀ p < 98280, ∀ p' < 98280, imgK arr (keyQ p) = imgK arr (keyQ p') → p = p' := by
    intro p1 hp1 p2 hp2 e
    obtain ⟨q1, hq1, e1, f1⟩ := hcov p1 hp1
    obtain ⟨q2, hq2, e2, f2⟩ := hcov p2 hp2
    have : q1 = q2 := hG.2 q1 hq1 q2 hq2 (e1.symm.trans (e.trans e2))
    subst this
    exact InitAux.xposK_inj hp1 hp2 (f1.symm.trans f2)
  have hsX : T.sgnX k < 2 ^ SX := by rw [hXs]; exact quadPl_lt _ _ _
  have hfA : ∀ y < SA, fA arr (Benes.benesPerm 10 (T.netA k) y) = y := fun y hy =>
    label_net (k := 10) hAn hAl (fun x hx b hb => testBit_labA hA hx hb) (fun x hx => fA_lt hA hx) hy
  have hfW : ∀ y < SX, fW arr (Benes.benesPerm 17 (T.netW k) y) = y := fun y hy =>
    label_net (k := 17) hWn hWl (fun x hx b hb => testBit_labW hA hx hb) (fun x hx => fW_lt hA hx) hy
  have hRinj : ∀ r < 4096, ∀ r' < 4096, rowP arr r = rowP arr r' → r = r' := by
    intro r hr r' hr' e
    have hf0 : ∀ s, fW arr (32 * s) = 32 * rowP arr s + arr[0]! := fun s => by
      unfold fW
      rw [ite_eq_left (by omega), show 32 * s / 32 = s by omega, show 32 * s % 32 = 0 by omega]
    have h1 : fW arr (32 * r) = fW arr (32 * r') := by rw [hf0, hf0, e]
    rw [label_inv hWn hfW (by rw [← SX_eq]; omega), label_inv hWn hfW (by rw [← SX_eq]; omega)] at h1
    have := congrArg (Benes.benesPerm 17 (T.netW k)) h1
    rw [Benes.benesPerm_benesInv hvW, Benes.benesPerm_benesInv hvW] at this
    omega
  have hsW : T.sgnW k < 2 ^ SX := by
    rw [hWs]
    exact Nat.lt_of_le_of_lt Nat.and_le_left valW_lt
  unfold RepN
  refine ⟨fun q hq => ?_, fun p0 hp0 hq0 => ?_, ?_, fun i hi j hj => ?_, fun y hy hyv => ?_, ?_,
    fun r' hr' j hj => ?_, fun y hy hyv => ?_, ?_⟩
  · change resPN 4 SX (ops15.net SX 17 (T.netX k) (ops15.neg SX (T.sgnX k) t.2.1)) (xposK q) =
      resM (hN 4) _ (300 + q)
    obtain ⟨p, hp, e, hpq⟩ := hkeyS q hq
    rw [ops15_law.net_res SX_eq hXn (ops15_law.neg_bd hsX hX3) (InitAux.xposK_lt' hq), e,
      ops15_law.neg_res hsX hX3 (InitAux.xposK_lt' hp), hX1 p hp,
      perm_resX h2 hv hG (fun p hp => (hcov p hp).imp fun q h => ⟨h.1, h.2.1⟩) hinj v hp hq hpq,
      sgnI_mul, hXs, quad_kappa hA (InitAux.xposK_lt' hp) (fun b hb => hK.ka p hp b hb)]
    rfl
  · change resPN 4 SX (ops15.net SX 17 (T.netX k) (ops15.neg SX (T.sgnX k) t.2.1)) p0 = 0
    have hx := hπX p0 hp0
    rw [ops15_law.net_res SX_eq hXn (ops15_law.neg_bd hsX hX3) hp0, ops15_law.neg_res hsX hX3 hx,
      hX2 _ hx (fun q hq e => by
        obtain ⟨q', hq', e'⟩ := hcovπ q hq
        exact hq0 q' hq' (hπXi _ _ (e'.trans e)))]
    simp
  · exact ops15_law.net_bd SX_eq hXn (ops15_law.neg_bd hsX hX3)
  · change resPN 4 SA (ops15.net SA 10 (T.netA k) t.2.2.1) (32 * i + j) = resM (hN 4) _ (Native.aIdx i j)
    have hy : 32 * i + j < SA := by rw [hSA]; omega
    have hx := hπA _ hy
    have hf := hfA _ hy
    set x := Benes.benesPerm 10 (T.netA k) (32 * i + j) with hxdef
    have hvx : x % 32 < 24 ∧ x / 32 < 24 := by
      by_contra hn
      unfold fA at hf
      rw [ite_eq_right hn] at hf
      rw [hf] at hn
      omega
    unfold fA at hf
    rw [ite_eq_left hvx] at hf
    have e1 : arr[x / 32]! = i := by have := hA.lt _ hvx.1; omega
    have e2 : arr[x % 32]! = j := by have := hA.lt _ hvx.1; omega
    have hi' : (Native.permInv arr)[i]! = x / 32 := by rw [← e1, hA.inv_arr hvx.2]
    have hj' : (Native.permInv arr)[j]! = x % 32 := by rw [← e2, hA.inv_arr hvx.1]
    have hA1' := hA1 _ hvx.2 _ hvx.1
    rw [show 32 * (x / 32) + x % 32 = x by omega] at hA1'
    rw [ops15_law.net_res SA_eq hAn hA3 hy, ← hxdef, perm_resA h2 hA v hi hj, hi', hj', hA1']
    rfl
  · change resPN 4 SA (ops15.net SA 10 (T.netA k) t.2.2.1) y = 0
    have hx := hπA _ hy
    have hf := hfA _ hy
    rw [ops15_law.net_res SA_eq hAn hA3 hy]
    by_cases hvx : (Benes.benesPerm 10 (T.netA k) y) % 32 < 24 ∧ (Benes.benesPerm 10 (T.netA k) y) / 32 < 24
    · exfalso
      unfold fA at hf
      rw [ite_eq_left hvx] at hf
      have := hA.lt _ hvx.1
      have := hA.lt _ hvx.2
      omega
    · unfold fA at hf
      rw [ite_eq_right hvx] at hf
      rw [hf]
      exact hA2 y hy hyv
  · exact ops15_law.net_bd SA_eq hAn hA3
  · change resPN 4 SX (ops15.net SX 17 (T.netW k) (ops15.neg SX (T.sgnW k) t.2.2.2)) (32 * r' + j) =
      resM (hN 4) _ (98580 + 24 * r' + j)
    have hy : 32 * r' + j < SX := by rw [hSX]; omega
    have hx := hπW _ hy
    have hf := hfW _ hy
    set x := Benes.benesPerm 17 (T.netW k) (32 * r' + j) with hxdef
    have hvx : x % 32 < 24 := by
      by_contra hn
      unfold fW at hf
      rw [ite_eq_right hn] at hf
      rw [hf] at hn
      omega
    unfold fW at hf
    rw [ite_eq_left hvx] at hf
    have hR : rowP arr (x / 32) = r' := by have := hA.lt _ hvx; omega
    have h2' : arr[x % 32]! = j := by have := hA.lt _ hvx; omega
    have hj' : (Native.permInv arr)[j]! = x % 32 := by rw [← h2', hA.inv_arr hvx]
    have hr : x / 32 < 4096 := by rw [hSX] at hx; omega
    have hxe : x = 32 * (x / 32) + x % 32 := by omega
    have hsg0 := testBit_sgW hA hr (Nat.mod_lt x (by decide))
    rw [← hxe] at hsg0
    have hsg : (T.sgnW k).testBit x = sgP arr (x / 32) := by
      rw [hWs]
      change (valW &&& sgW P).testBit x = _
      rw [Nat.testBit_and, testBit_valW, decide_eq_true ⟨hx, hvx⟩, Bool.true_and, hsg0]
      rfl
    have hw := perm_resW h2 hA hRinj v hr hj
    rw [hR, hj'] at hw
    have hW1' := hW1 _ hr _ hvx
    rw [← hxe] at hW1'
    rw [ops15_law.net_res SX_eq hWn (ops15_law.neg_bd hsW hW3) hy, ← hxdef,
      ops15_law.neg_res hsW hW3 hx, hsg, hw, sgnI_mul, hW1']
    rfl
  · change resPN 4 SX (ops15.net SX 17 (T.netW k) (ops15.neg SX (T.sgnW k) t.2.2.2)) y = 0
    have hx := hπW _ hy
    have hf := hfW _ hy
    rw [ops15_law.net_res SX_eq hWn (ops15_law.neg_bd hsW hW3) hy, ops15_law.neg_res hsW hW3 hx]
    by_cases hvx : (Benes.benesPerm 17 (T.netW k) y) % 32 < 24
    · exfalso
      unfold fW at hf
      rw [ite_eq_left hvx] at hf
      have := hA.lt _ hvx
      omega
    · unfold fW at hf
      rw [ite_eq_right hvx] at hf
      rw [hf, hW2 y hy hyv]
      simp
  · exact ops15_law.net_bd SX_eq hWn (ops15_law.neg_bd hsW hW3)

end CFSG.KC.KStep

end
