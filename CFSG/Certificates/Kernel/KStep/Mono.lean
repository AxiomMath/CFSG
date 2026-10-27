module

public import CFSG.Certificates.Kernel.KStep.Native
public import CFSG.Certificates.Kernel.KStep.Laws
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.Trace6091.TwinEq
public import CFSG.Monster.B.Rep4371.GlueDefs
import CFSG.Certificates.Kernel.KDense.KeysSound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP
open CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371.Native
open CFSG.KC.MonsterConv.Perm

namespace MonoAux

open CFSG.KC.Benes (nxor nland nlor nshl nshr nmul nadd nsub ndiv)

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
  rw [combN_two_pow, if_pos hi]

theorem permDN_lin (p : Array ℕ) (d : ℕ) : permDN p d = combN (fun i => permDN p (2 ^ i)) 12 d := by
  have hL : ∀ x y, dualN (permWordN p (x ^^^ y)) = dualN (permWordN p x) ^^^ dualN (permWordN p y) :=
    fun x y => by rw [permWordN_xor, dualN_xor]
  have h0 : dualN (permWordN p 0) = 0 := by rw [permWordN_zero, dualN_zero]
  have e := combN_map (L := fun x => dualN (permWordN p x)) hL h0 umaskN d 12
  refine e.trans (combN_congr d fun i hi => ?_)
  change dualN (permWordN p (umaskN i)) = dualN (permWordN p (combN umaskN 12 (2 ^ i)))
  rw [combN_two_pow, if_pos hi]

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
  · change f (Nat.shiftLeft 1 k) < _
    rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]
    exact hf k hk
  · change (f (Nat.shiftLeft 1 i)).testBit k = _
    rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]

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
  change _ = (decide (i < j) && x.testBit i && x.testBit j && BT.testBit (12 * i + j))
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

theorem muxLoop_lt {S n m : ℕ} (hm : m < 2 ^ S) (sel idp : ℕ → ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc (Nat.shiftLeft (mux S m (sel b) (idp b))
      (Nat.mul b S))) n < 2 ^ (n * S) :=
  planeLoop_lt (fun b => mux S m (sel b) (idp b)) (fun b => Nat.mul b S) (fun _ => rfl)
    (fun _ _ => mux_lt hm)

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

theorem testBit_idP {k b p : ℕ} (hb : b < k) (hp : p < 2 ^ k) :
    (idP k).testBit (b * 2 ^ k + p) = p.testBit b := by
  unfold idP
  refine (testBit_planeLoop (S := 2 ^ k) (n := k) (fun b => idPlane (Nat.shiftLeft 1 k) b)
    (fun b => Nat.mul b (Nat.shiftLeft 1 k))
    (fun b => by rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]; rfl)
    (fun b hb => by rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]; exact idPlane_lt' hb) hb hp).trans ?_
  change (idPlane (Nat.shiftLeft 1 k) b).testBit p = _
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

theorem bit_lt {m S p : ℕ} (hm : m < 2 ^ S) (h : m.testBit p = true) : p < S := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h
  exact absurd h (by decide)

theorem lt_of_bits {x n : ℕ} (h : ∀ i, x.testBit i = true → i < n) : x < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    cases hx : x.testBit i
    · rfl
    · exact absurd (h i hx) (by omega)

theorem bit_hi {x n i : ℕ} (hx : x < 2 ^ n) (hi : n ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

theorem add_pow_xor {x c : ℕ} (h : x.testBit c = false) : x + 2 ^ c = x ^^^ 2 ^ c := by
  have hr : x % 2 ^ (c + 1) < 2 ^ c := by
    have h1 := Nat.mod_lt x (Nat.two_pow_pos (c + 1))
    have h2 := Benes.testBit_top h1
    rw [Nat.testBit_mod_two_pow, decide_eq_true (Nat.lt_succ_self c), Bool.true_and, h] at h2
    by_contra hc
    rw [decide_eq_true (by omega)] at h2
    exact absurd h2 (by decide)
  have e := Nat.div_add_mod x (2 ^ (c + 1))
  have h2c : 2 ^ (c + 1) = 2 ^ c + 2 ^ c := by rw [Nat.pow_succ, Nat.mul_two]
  have hlt : x % 2 ^ (c + 1) + 2 ^ c < 2 ^ (c + 1) := by omega
  have e2 : x + 2 ^ c = 2 ^ (c + 1) * (x / 2 ^ (c + 1)) + (x % 2 ^ (c + 1) ||| 2 ^ c) := by
    rw [Nat.or_two_pow_eq_add_of_lt hr]
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [e2, Nat.testBit_two_pow_mul_add _ (by rw [Nat.or_two_pow_eq_add_of_lt hr]; exact hlt),
    Nat.testBit_xor, Nat.testBit_two_pow]
  conv_rhs => rw [← e]
  rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  split
  · rw [Nat.testBit_or, Nat.testBit_two_pow]
    by_cases hi : c = i
    · subst hi
      rw [Nat.testBit_lt_two_pow hr]
      simp
    · rw [decide_eq_false hi, Bool.or_false, Bool.xor_false]
  · rw [decide_eq_false (by omega), Bool.xor_false]

theorem sub_pow_xor {x c : ℕ} (h : x.testBit c = true) : x - 2 ^ c = x ^^^ 2 ^ c := by
  have h1 : (x ^^^ 2 ^ c).testBit c = false := by
    rw [Nat.testBit_xor, h, Nat.testBit_two_pow, decide_eq_true rfl]
    rfl
  have e := add_pow_xor h1
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at e
  omega

theorem testBit_idPlane {K b p : ℕ} (hb : b < K) :
    (idPlane (2 ^ K) b).testBit p = (decide (p < 2 ^ K) && p.testBit b) :=
  Benes.idPlane_testBit hb p

theorem testBit_clrN {K b p : ℕ} (hb : b < K) :
    (clrN (2 ^ K) b).testBit p = (decide (p < 2 ^ K) && !p.testBit b) := by
  unfold clrN
  rw [nxor, Nat.testBit_xor, testBit_ones, testBit_idPlane hb]
  cases decide (p < 2 ^ K) <;> cases p.testBit b <;> rfl

theorem validIn_xor {K d e m : ℕ} (he : e < 2 ^ K)
    (h : ∀ p, m.testBit p = true → p < 2 ^ K ∧ p + d = p ^^^ e ∧ m.testBit (p ^^^ e) = false) :
    Benes.ValidIn (2 ^ K) d m := fun p hp => by
  obtain ⟨h1, h2, h3⟩ := h p hp
  rw [h2]
  exact ⟨Nat.xor_lt_two_pow h1 he, h3⟩

theorem validIn_landL {S d m : ℕ} (R : ℕ) (h : Benes.ValidIn S d m) :
    Benes.ValidIn S d (Nat.land R m) := fun p hp => by
  rw [nland, Nat.testBit_and, Bool.and_eq_true] at hp
  obtain ⟨h1, h2⟩ := h p hp.2
  refine ⟨h1, ?_⟩
  rw [nland, Nat.testBit_and, h2, Bool.and_false]

theorem validIn_landR {S d m : ℕ} (R : ℕ) (h : Benes.ValidIn S d m) :
    Benes.ValidIn S d (Nat.land m R) := fun p hp => by
  rw [nland, Nat.testBit_and, Bool.and_eq_true] at hp
  obtain ⟨h1, h2⟩ := h p hp.1
  refine ⟨h1, ?_⟩
  rw [nland, Nat.testBit_and, h2, Bool.false_and]

theorem pow_lt_pow {a K : ℕ} (h : a < K) : 2 ^ a < 2 ^ K := Nat.pow_lt_pow_right (by norm_num) h

theorem validIn_bx {K a b : ℕ} (hab : a < b) (hb : b < K) :
    Benes.ValidIn (2 ^ K) (Nat.sub (Nat.shiftLeft 1 b) (Nat.shiftLeft 1 a))
      (Nat.land (idPlane (2 ^ K) a) (clrN (2 ^ K) b)) := by
  have hd : Nat.sub (Nat.shiftLeft 1 b) (Nat.shiftLeft 1 a) = 2 ^ b - 2 ^ a := by
    simp only [nsub, nshl, Nat.one_shiftLeft]
  rw [hd]
  refine validIn_xor (e := 2 ^ a ^^^ 2 ^ b)
    (Nat.xor_lt_two_pow (pow_lt_pow (by omega)) (pow_lt_pow hb)) fun p hp => ?_
  rw [nland, Nat.testBit_and, testBit_idPlane (b := a) (by omega), testBit_clrN hb] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨hp1, ha⟩, -, hbb⟩ := hp
  refine ⟨hp1, ?_, ?_⟩
  · have h1 : 2 ^ a ≤ p := Nat.ge_two_pow_of_testBit ha
    have h2 : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab.le
    have e1 : p - 2 ^ a = p ^^^ 2 ^ a := sub_pow_xor ha
    have hb' : (p ^^^ 2 ^ a).testBit b = false := by
      rw [Nat.testBit_xor, hbb, Nat.testBit_two_pow, decide_eq_false (by omega)]
      rfl
    have e2 := add_pow_xor hb'
    rw [← e1] at e2
    rw [← Nat.xor_assoc, ← e1, ← e2]
    omega
  · rw [nland, Nat.testBit_and, testBit_idPlane (K := K) (b := a) (by omega), ← Nat.xor_assoc, Nat.testBit_xor,
      Nat.testBit_xor, ha, Nat.testBit_two_pow, Nat.testBit_two_pow, decide_eq_true rfl,
      decide_eq_false (by omega : ¬ b = a)]
    simp

theorem validIn_flip {K c : ℕ} (hc : c < K) :
    Benes.ValidIn (2 ^ K) (Nat.shiftLeft 1 c) (clrN (2 ^ K) c) := by
  have hd : Nat.shiftLeft 1 c = 2 ^ c := by simp only [nshl, Nat.one_shiftLeft]
  rw [hd]
  refine validIn_xor (e := 2 ^ c) (pow_lt_pow hc) fun p hp => ?_
  rw [testBit_clrN hc] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
  refine ⟨hp.1, add_pow_xor hp.2, ?_⟩
  rw [testBit_clrN hc, Nat.testBit_xor, hp.2, Nat.testBit_two_pow, decide_eq_true rfl]
  simp

theorem validIn_flip2 {K c1 c2 : ℕ} (h12 : c1 ≠ c2) (h1 : c1 < K) (h2 : c2 < K) :
    Benes.ValidIn (2 ^ K) (Nat.add (Nat.shiftLeft 1 c1) (Nat.shiftLeft 1 c2))
      (Nat.land (clrN (2 ^ K) c1) (clrN (2 ^ K) c2)) := by
  have hd : Nat.add (Nat.shiftLeft 1 c1) (Nat.shiftLeft 1 c2) = 2 ^ c1 + 2 ^ c2 := by
    simp only [nadd, nshl, Nat.one_shiftLeft]
  rw [hd]
  refine validIn_xor (e := 2 ^ c1 ^^^ 2 ^ c2)
    (Nat.xor_lt_two_pow (pow_lt_pow h1) (pow_lt_pow h2)) fun p hp => ?_
  rw [nland, Nat.testBit_and, testBit_clrN h1, testBit_clrN h2] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨hp1, ha⟩, -, hb⟩ := hp
  refine ⟨hp1, ?_, ?_⟩
  · have hb' : (p ^^^ 2 ^ c1).testBit c2 = false := by
      rw [Nat.testBit_xor, hb, Nat.testBit_two_pow, decide_eq_false h12]
      rfl
    rw [← Nat.xor_assoc, ← add_pow_xor hb', ← add_pow_xor ha]
    omega
  · rw [nland, Nat.testBit_and, testBit_clrN h1, ← Nat.xor_assoc, Nat.testBit_xor, Nat.testBit_xor,
      ha, Nat.testBit_two_pow, Nat.testBit_two_pow, decide_eq_true rfl,
      decide_eq_false (Ne.symm h12)]
    simp

theorem validIn_net {K k N i : ℕ} (R : ℕ) (hk : k ≤ K) (hN : netOK k N = true) (hi : i < 2 * k - 1) :
    Benes.ValidIn (2 ^ K) (stageShift k i)
      (Nat.land R (Nat.mul (Nat.land (Nat.shiftRight N (Nat.mul i (Nat.shiftLeft 1 k)))
        (ones (Nat.shiftLeft 1 k))) (repLow (2 ^ K) k))) := by
  have hbm : Nat.land (Nat.shiftRight N (Nat.mul i (Nat.shiftLeft 1 k))) (ones (Nat.shiftLeft 1 k)) =
      Benes.benesMask k N i := by
    simp only [Benes.benesMask, nshl, Nat.one_shiftLeft]
  have hW : (2 : ℕ) ^ K = 2 ^ k * 2 ^ (K - k) := by rw [← Nat.pow_add]; congr 1; omega
  have hU : repLow (2 ^ K) k = (2 ^ (2 ^ K) - 1) / (2 ^ (2 ^ k) - 1) := by
    unfold repLow
    rw [Benes.repU_eq]
    simp only [nshl, ndiv, Nat.one_shiftLeft]
    rw [Nat.mul_div_cancel' (Nat.pow_dvd_pow 2 hk)]
  have hbl : Benes.benesMask k N i < 2 ^ (2 ^ k) := by
    unfold Benes.benesMask
    rw [nland, Benes.ones_eq]
    exact Benes.land_ones_lt _ _
  have hmb : ∀ q, (Nat.mul (Benes.benesMask k N i) (repLow (2 ^ K) k)).testBit q =
      (decide (q < 2 ^ K) && (Benes.benesMask k N i).testBit (q % 2 ^ k)) := by
    intro q
    rw [nmul, hU]
    exact Benes.testBit_mul_div (L := 2 ^ k) (n := 2 ^ (K - k)) (Nat.two_pow_pos _) hW hbl q
  have hv := Benes.stagesValid_of_netOK hN i hi
  rw [hbm]
  intro p hp
  rw [nland, Nat.testBit_and, hmb, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨-, hp1, hp2⟩ := hp
  obtain ⟨hv1, hv2⟩ := hv _ hp2
  have e := Nat.div_add_mod p (2 ^ k)
  have ha : p / 2 ^ k < 2 ^ (K - k) :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).2 (by rw [Nat.mul_comm, ← hW]; exact hp1)
  have h3 : 2 ^ k * (p / 2 ^ k + 1) ≤ 2 ^ k * 2 ^ (K - k) := Nat.mul_le_mul_left _ ha
  rw [Nat.mul_succ, ← hW] at h3
  refine ⟨by omega, ?_⟩
  rw [nland, Nat.testBit_and, hmb, Benes.mod_add_lt hv1, hv2]
  simp

structure Gat (S T : ℕ) (f : ℕ → ℕ → ℕ) (π : ℕ → ℕ) (Z : ℕ → Bool) : Prop where
  lt : ∀ x < T, π x < S
  bit : ∀ np X b x, b < np → x < T →
    (f np X).testBit (b * T + x) = (!Z x && X.testBit (b * S + π x))
  bd : ∀ np X, X < 2 ^ (np * S) → f np X < 2 ^ (np * T)

structure PG (S : ℕ) (f : ℕ → ℕ → ℕ) (π : ℕ → ℕ) : Prop where
  g : Gat S S f π (fun _ => false)
  inj : ∀ x < S, ∀ y < S, π x = π y → x = y

theorem Gat.comp {S T U : ℕ} {f g : ℕ → ℕ → ℕ} {π1 π2 : ℕ → ℕ} {Z1 Z2 : ℕ → Bool}
    (hg : Gat S T g π1 Z1) (hf : Gat T U f π2 Z2) :
    Gat S U (fun np X => f np (g np X)) (fun x => π1 (π2 x)) (fun x => Z2 x || Z1 (π2 x)) where
  lt x hx := hg.lt _ (hf.lt x hx)
  bit np X b x hb hx := by
    rw [hf.bit np _ b x hb hx, hg.bit np X b _ hb (hf.lt x hx)]
    cases Z2 x <;> cases Z1 (π2 x) <;> rfl
  bd np X hX := hf.bd np _ (hg.bd np X hX)

theorem Gat.congr {S T : ℕ} {f : ℕ → ℕ → ℕ} {π π' : ℕ → ℕ} {Z Z' : ℕ → Bool} (h : Gat S T f π Z)
    (hπ : ∀ x < T, π' x = π x) (hZ : ∀ x < T, Z' x = Z x) : Gat S T f π' Z' where
  lt x hx := by rw [hπ x hx]; exact h.lt x hx
  bit np X b x hb hx := by rw [hπ x hx, hZ x hx]; exact h.bit np X b x hb hx
  bd := h.bd

theorem Gat.congrF {S T : ℕ} {f f' : ℕ → ℕ → ℕ} {π : ℕ → ℕ} {Z : ℕ → Bool} (h : Gat S T f π Z)
    (hf : ∀ np X, f' np X = f np X) : Gat S T f' π Z where
  lt := h.lt
  bit np X b x hb hx := by rw [hf]; exact h.bit np X b x hb hx
  bd np X hX := by rw [hf]; exact h.bd np X hX

theorem Gat.union {S T : ℕ} {f g : ℕ → ℕ → ℕ} {π1 π2 : ℕ → ℕ} {Z1 Z2 : ℕ → Bool}
    (hf : Gat S T f π1 Z1) (hg : Gat S T g π2 Z2) (hd : ∀ x < T, Z1 x = true ∨ Z2 x = true) :
    Gat S T (fun np X => f np X ||| g np X) (fun x => if Z1 x = true then π2 x else π1 x)
      (fun x => Z1 x && Z2 x) where
  lt x hx := by
    split
    · exact hg.lt x hx
    · exact hf.lt x hx
  bit np X b x hb hx := by
    rw [Nat.testBit_or, hf.bit np X b x hb hx, hg.bit np X b x hb hx]
    rcases hd x hx with h | h <;> cases h1 : Z1 x <;> cases h2 : Z2 x <;> simp_all
  bd np X hX := Nat.or_lt_two_pow (hf.bd np X hX) (hg.bd np X hX)

theorem PG.gat {S : ℕ} {f : ℕ → ℕ → ℕ} {π : ℕ → ℕ} (h : PG S f π) : Gat S S f π (fun _ => false) := h.g

theorem PG.comp {S : ℕ} {f g : ℕ → ℕ → ℕ} {π1 π2 : ℕ → ℕ} (hg : PG S g π1) (hf : PG S f π2) :
    PG S (fun np X => f np (g np X)) (fun x => π1 (π2 x)) where
  g := (Gat.comp hg.g hf.g).congr (fun _ _ => rfl) (fun _ _ => rfl)
  inj x hx y hy h := hf.inj x hx y hy (hg.inj _ (hf.g.lt x hx) _ (hf.g.lt y hy) h)

theorem PG.congrF {S : ℕ} {f f' : ℕ → ℕ → ℕ} {π : ℕ → ℕ} (h : PG S f π)
    (hf : ∀ np X, f' np X = f np X) : PG S f' π where
  g := h.g.congrF hf
  inj := h.inj

theorem pg_id (S : ℕ) : PG S (fun _ X => X) id where
  g := ⟨fun _ hx => hx, fun _ _ _ _ _ _ => rfl, fun _ _ hX => hX⟩
  inj _ _ _ _ h := h

theorem repN_rep {S m : ℕ} (hm : m < 2 ^ S) (n : ℕ) : Benes.Rep S n (repN S n m) m :=
  Benes.rep_repP (fun p hp => bit_lt hm hp) n

theorem rep_bit {S n M m b x : ℕ} (hR : Benes.Rep S n M m) (hb : b < n) (hx : x < S) :
    M.testBit (b * S + x) = m.testBit x := by
  have h1 : S * b + x < S * n := by
    have : S * (b + 1) ≤ S * n := Nat.mul_le_mul_left _ hb
    rw [Nat.mul_succ] at this
    omega
  rw [hR, Nat.mul_comm b S, Nat.mul_add_mod, Nat.mod_eq_of_lt hx, decide_eq_true h1, Bool.true_and]

theorem pg_dsw {S d m : ℕ} (hv : Benes.ValidIn S d m) :
    PG S (fun np X => dsw d (repN S np m) X) (Benes.swp d m) where
  g := {
    lt := fun x hx => Benes.swp_lt hv hx
    bit := fun np X b x hb hx => by
      have hR := repN_rep (Benes.lt_of_validIn hv) np
      rw [Benes.testBit_dsw (Benes.rep_disj hR hv), Nat.mul_comm b S, Benes.swp_rep hR hv hb hx]
      rfl
    bd := fun np X hX => by
      have hR := repN_rep (Benes.lt_of_validIn hv) np
      refine Nat.lt_pow_two_of_testBit _ fun q hq => ?_
      rw [Benes.testBit_dsw (Benes.rep_disj hR hv),
        Benes.swp_rep_hi hR hv (by rw [Nat.mul_comm]; exact hq)]
      exact bit_hi hX hq }
  inj x _ y _ h := by
    have := congrArg (Benes.swp d m) h
    rwa [Benes.swp_swp (Benes.validIn_disj hv), Benes.swp_swp (Benes.validIn_disj hv)] at this

theorem gat_mask {S m : ℕ} (hm : m < 2 ^ S) :
    Gat S S (fun np X => X &&& repN S np m) id (fun x => !m.testBit x) where
  lt _ hx := hx
  bit np X b x hb hx := by
    rw [Nat.testBit_and, rep_bit (repN_rep hm np) hb hx, id, Bool.not_not, Bool.and_comm]
  bd np X hX := Nat.lt_of_le_of_lt Nat.and_le_left hX

def preIt (g : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => preIt g n (g n x)

def postIt (g : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => g n (postIt g n x)

def preC (τ : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => τ n (preC τ n x)

def postC (τ : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => postC τ n (τ n x)

theorem pg_preIt {S : ℕ} {g : ℕ → ℕ → ℕ → ℕ} {τ : ℕ → ℕ → ℕ} : ∀ n,
    (∀ k < n, PG S (g k) (τ k)) → PG S (fun np X => preIt (fun k => g k np) n X) (preC τ n)
  | 0, _ => (pg_id S).congrF fun _ _ => rfl
  | n + 1, h => (PG.comp (h n (by omega)) (pg_preIt n fun k hk => h k (by omega))).congrF
      fun _ _ => rfl

theorem pg_postIt {S : ℕ} {g : ℕ → ℕ → ℕ → ℕ} {τ : ℕ → ℕ → ℕ} : ∀ n,
    (∀ k < n, PG S (g k) (τ k)) → PG S (fun np X => postIt (fun k => g k np) n X) (postC τ n)
  | 0, _ => (pg_id S).congrF fun _ _ => rfl
  | n + 1, h => (PG.comp (pg_postIt n fun k hk => h k (by omega)) (h n (by omega))).congrF
      fun _ _ => rfl

theorem rec_pre0 (G : ℕ → ℕ → ℕ) : ∀ j y, Nat.rec (motive := fun _ => ℕ → ℕ) (fun y => y)
    (fun j ih y => ih (G j y)) j y = preIt G j y
  | 0, _ => rfl
  | j + 1, y => rec_pre0 G j (G j y)

theorem rec_pre1 (G : ℕ → ℕ → ℕ) : ∀ j y, Nat.rec (motive := fun _ => ℕ → ℕ) (fun y => y)
    (fun j ih y => CFSG.KC.Loop.strictN (G j y) ih) j y = preIt G j y
  | 0, _ => rfl
  | j + 1, y => by
    change _ = preIt G j (G j y)
    rw [← rec_pre1 G j (G j y)]
    exact Benes.strictN_eq _ _

theorem rec_post (G : ℕ → ℕ → ℕ) : ∀ j y, Nat.rec (motive := fun _ => ℕ → ℕ) (fun z => z)
    (fun s ih z => CFSG.KC.Loop.strictN (ih z) (fun w => G s w)) j y = postIt G j y
  | 0, _ => rfl
  | j + 1, y => by
    change _ = G j (postIt G j y)
    rw [← rec_post G j y]
    exact Benes.strictN_eq _ _

theorem pg_strict {S : ℕ} {f : ℕ → ℕ → ℕ} {π : ℕ → ℕ} (h : PG S f π) :
    PG S (fun np X => CFSG.KC.Loop.strictN (f np X) (fun z => z)) π :=
  h.congrF fun _ _ => Benes.strictN_eq _ _

theorem pg_netRepN {S K k : ℕ} (hS : S = 2 ^ K) (hk : k ≤ K) {N : ℕ} (hN : netOK k N = true)
    (R : ℕ) : ∃ π, PG S (fun np X => netRepN S np k (repLow S k) R N X) π := by
  subst hS
  exact ⟨_, (pg_preIt (2 * k - 1) (g := fun j np y => dsw (stageShift k (Nat.sub (Nat.sub (Nat.mul 2 k) 2) j))
      (repN (2 ^ K) np (Nat.land R (Nat.mul (Nat.land (Nat.shiftRight N
        (Nat.mul (Nat.sub (Nat.sub (Nat.mul 2 k) 2) j) (Nat.shiftLeft 1 k))) (ones (Nat.shiftLeft 1 k)))
          (repLow (2 ^ K) k)))) y)
    fun j hj => pg_dsw (validIn_net R hk hN (by simp only [nsub, nmul]; omega))).congrF
      fun np X => rec_pre1 _ _ X⟩

theorem pg_bswapN {K a b : ℕ} (hab : a < b) (hb : b < K) (R : ℕ) :
    PG (2 ^ K) (fun np X => bswapN (2 ^ K) np a b R X)
      (Benes.swp (Nat.sub (Nat.shiftLeft 1 b) (Nat.shiftLeft 1 a))
        (Nat.land R (Nat.land (idPlane (2 ^ K) a) (clrN (2 ^ K) b)))) :=
  pg_dsw (validIn_landL R (validIn_bx hab hb))

theorem pg_revN {S K lo w : ℕ} (hS : S = 2 ^ K) (hw : lo + w ≤ K) (R : ℕ) :
    ∃ π, PG S (fun np X => revN S np lo w R X) π := by
  subst hS
  exact ⟨_, (pg_preIt (w / 2) (g := fun k np y => CFSG.KC.Loop.strictN
      (bswapN (2 ^ K) np (Nat.add lo k) (Nat.sub (Nat.add lo (Nat.sub w 1)) k) R y) (fun z => z))
    fun k hk => pg_strict (pg_bswapN (by simp only [nadd, nsub]; omega)
      (by simp only [nadd, nsub]; omega) R)).congrF fun np X => rec_pre0 _ _ X⟩

theorem pg_rotrN {S K lo w r : ℕ} (hS : S = 2 ^ K) (hw : lo + w ≤ K) (hr : r ≤ w) (R : ℕ) :
    ∃ π, PG S (fun np X => rotrN S np lo w r R X) π := by
  obtain ⟨π1, h1⟩ := pg_revN (lo := lo) (w := w) hS hw R
  obtain ⟨π2, h2⟩ := pg_revN (lo := lo) (w := Nat.sub w r) hS (by simp only [nsub]; omega) R
  obtain ⟨π3, h3⟩ := pg_revN (lo := Nat.add lo (Nat.sub w r)) (w := r) hS
    (by simp only [nsub, nadd]; omega) R
  exact ⟨_, (PG.comp (PG.comp h1 h2) h3).congrF fun _ _ => rfl⟩

theorem qPl_eq (b : ℕ) : qPl b = idPlane (2 ^ 17) (10 + b) := rfl

theorem qClr_eq (b : ℕ) : qClr b = clrN (2 ^ 17) (10 + b) := rfl

theorem pg_opJK {u v : ℕ} (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ 6) (M : ℕ) :
    ∃ π, PG SX (fun np X => opJK np u v M X) π := by
  have e1 : qPl (Nat.sub u 1) = idPlane (2 ^ 17) (Nat.add 9 u) := by
    rw [qPl_eq]; congr 1; simp only [nadd, nsub]; omega
  have e2 : qClr (Nat.sub v 1) = clrN (2 ^ 17) (Nat.add 9 v) := by
    rw [qClr_eq]; congr 1; simp only [nadd, nsub]; omega
  have hv' := validIn_landL M (validIn_bx (K := 17) (a := Nat.add 9 u) (b := Nat.add 9 v)
    (by simp only [nadd]; omega) (by simp only [nadd]; omega))
  rw [← e1, ← e2] at hv'
  exact ⟨_, pg_dsw hv'⟩

theorem pg_op0K {v : ℕ} (hv1 : 1 ≤ v) (hv : v ≤ 6) (M : ℕ) :
    ∃ π, PG SX (fun np X => op0K np v M X) π := by
  have e2 : qClr (Nat.sub v 1) = clrN (2 ^ 17) (Nat.add 9 v) := by
    rw [qClr_eq]; congr 1; simp only [nadd, nsub]; omega
  have hv' := validIn_landL M (validIn_landR qPar (validIn_flip (K := 17) (c := Nat.add 9 v)
    (by simp only [nadd]; omega)))
  rw [← e2] at hv'
  exact ⟨_, pg_dsw hv'⟩

theorem pg_opJ7 {u : ℕ} (hu : 1 ≤ u) (hu6 : u ≤ 6) (M : ℕ) :
    ∃ π, PG SX (fun np X => opJ7 np u M X) π := by
  have hst : ∀ b < 6, ∃ τ, PG SX (fun np y => Bool.rec (motive := fun _ => ℕ)
      (CFSG.KC.Loop.strictN (dsw (Nat.shiftLeft 1 (Nat.add 10 b))
        (repN SX np (Nat.land M (Nat.land (qClr b) (qPl (Nat.sub u 1))))) y) (fun z => z))
      y (Nat.beq b (Nat.sub u 1))) τ := by
    intro b hb
    cases Nat.beq b (Nat.sub u 1)
    · exact ⟨_, pg_strict (pg_dsw (validIn_landL M (validIn_landR _ (validIn_flip (K := 17)
        (c := Nat.add 10 b) (by simp only [nadd]; omega)))))⟩
    · exact ⟨_, pg_id SX⟩
  choose τ hτ using hst
  exact ⟨_, (pg_preIt 6 (τ := fun k => if h : k < 6 then τ k h else id)
    (g := fun b np y => Bool.rec (motive := fun _ => ℕ)
      (CFSG.KC.Loop.strictN (dsw (Nat.shiftLeft 1 (Nat.add 10 b))
        (repN SX np (Nat.land M (Nat.land (qClr b) (qPl (Nat.sub u 1))))) y) (fun z => z))
      y (Nat.beq b (Nat.sub u 1)))
    fun k hk => by rw [dite_eq_left hk]; exact hτ k hk).congrF fun np X => by
      rw [← rec_pre0]
      rfl⟩

theorem pg_op07 (M : ℕ) : ∃ π, PG SX (fun np X => op07 np M X) π := by
  have hst : ∀ k < 3, ∃ τ, PG SX (fun np y => (fun a b => CFSG.KC.Loop.strictN
        (dsw (Nat.sub (Nat.shiftLeft 1 (Nat.add 10 b)) (Nat.shiftLeft 1 (Nat.add 10 a)))
          (repN SX np (Nat.land M (Nat.land qPar (Nat.land (qPl a) (qClr b)))))
          (dsw (Nat.add (Nat.shiftLeft 1 (Nat.add 10 a)) (Nat.shiftLeft 1 (Nat.add 10 b)))
            (repN SX np (Nat.land M (Nat.land qPar (Nat.land (qClr a) (qClr b))))) y)) (fun z => z))
      (Nat.mul 2 k) (Nat.add (Nat.mul 2 k) 1)) τ := by
    intro k hk
    have h1 := pg_dsw (validIn_landL M (validIn_landL qPar (validIn_flip2 (K := 17)
      (c1 := Nat.add 10 (Nat.mul 2 k)) (c2 := Nat.add 10 (Nat.add (Nat.mul 2 k) 1))
      (by simp only [nadd, nmul]; omega) (by simp only [nadd, nmul]; omega)
      (by simp only [nadd, nmul]; omega))))
    have h2 := pg_dsw (validIn_landL M (validIn_landL qPar (validIn_bx (K := 17)
      (a := Nat.add 10 (Nat.mul 2 k)) (b := Nat.add 10 (Nat.add (Nat.mul 2 k) 1))
      (by simp only [nadd, nmul]; omega) (by simp only [nadd, nmul]; omega))))
    exact ⟨_, pg_strict (PG.comp h1 h2)⟩
  choose τ hτ using hst
  exact ⟨_, (pg_preIt 3 (τ := fun k => if h : k < 3 then τ k h else id)
    (g := fun k np y => (fun a b => CFSG.KC.Loop.strictN
        (dsw (Nat.sub (Nat.shiftLeft 1 (Nat.add 10 b)) (Nat.shiftLeft 1 (Nat.add 10 a)))
          (repN SX np (Nat.land M (Nat.land qPar (Nat.land (qPl a) (qClr b)))))
          (dsw (Nat.add (Nat.shiftLeft 1 (Nat.add 10 a)) (Nat.shiftLeft 1 (Nat.add 10 b)))
            (repN SX np (Nat.land M (Nat.land qPar (Nat.land (qClr a) (qClr b))))) y)) (fun z => z))
      (Nat.mul 2 k) (Nat.add (Nat.mul 2 k) 1))
    fun k hk => by rw [dite_eq_left hk]; exact hτ k hk).congrF fun np X => by
      rw [← rec_pre0]
      rfl⟩

theorem beq_t {a b : ℕ} (h : a = b) : Nat.beq a b = true := by rw [Nat.beq_eq]; exact h

theorem beq_f {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]; exact h

theorem pg_opT {u v : ℕ} (huv : u < v) (hv : v < 8) (M : ℕ) :
    ∃ π, PG SX (fun np X => opT np u v M X) π := by
  by_cases h7 : v = 7 <;> by_cases h0 : u = 0
  · obtain ⟨π, h⟩ := pg_op07 M
    exact ⟨π, h.congrF fun np X => by unfold opT; rw [beq_t h7, beq_t h0]⟩
  · obtain ⟨π, h⟩ := pg_opJ7 (u := u) (by omega) (by omega) M
    exact ⟨π, h.congrF fun np X => by unfold opT; rw [beq_t h7, beq_f h0]⟩
  · obtain ⟨π, h⟩ := pg_op0K (v := v) (by omega) (by omega) M
    exact ⟨π, h.congrF fun np X => by unfold opT; rw [beq_f h7, beq_t h0]⟩
  · obtain ⟨π, h⟩ := pg_opJK (u := u) (v := v) (by omega) huv (by omega) M
    exact ⟨π, h.congrF fun np X => by unfold opT; rw [beq_f h7, beq_f h0]⟩

theorem slotUV_ok : ∀ s < 20, Nat.div (slotUV s) 8 < Nat.mod (slotUV s) 8 := by decide +kernel

theorem pg_octSlots (E : MonoE) : ∃ π, PG SX (fun np X => octSlots np E X) π := by
  have hs : ∀ s < 20, ∃ τ, PG SX (fun np w => (fun uv => opT np (Nat.div uv 8) (Nat.mod uv 8)
      (selRep E.sel s) w) (slotUV s)) τ := fun s hs =>
    pg_opT (slotUV_ok s hs) (Nat.mod_lt _ (by decide)) _
  choose τ hτ using hs
  have hf : ∀ b < 6, PG SX (fun np z => CFSG.KC.Loop.strictN (dsw (Nat.shiftLeft 1 (Nat.add 10 b))
        (repN SX np (Nat.land (selRep E.xsel b) (qClr b))) z) (fun w => w))
      (Benes.swp (Nat.shiftLeft 1 (Nat.add 10 b)) (Nat.land (selRep E.xsel b) (qClr b))) :=
    fun b hb => pg_strict (pg_dsw (validIn_landL _ (validIn_flip (K := 17) (c := Nat.add 10 b)
      (by simp only [nadd]; omega))))
  have h1 := pg_postIt 20 (τ := fun k => if h : k < 20 then τ k h else id)
    (g := fun s np w => (fun uv => opT np (Nat.div uv 8) (Nat.mod uv 8) (selRep E.sel s) w) (slotUV s))
    fun k hk => by rw [dite_eq_left hk]; exact hτ k hk
  have h2 := pg_preIt 6 hf
  exact ⟨_, (PG.comp h1 h2).congrF fun np X => by
    rw [← rec_post, ← rec_pre0]
    rfl⟩

theorem testBit_chunks {F off : ℕ → ℕ} {c L W : ℕ} (hF : ∀ b, F b < 2 ^ L) (hoff : ∀ b, off b = c + b * W)
    (hcW : c + L ≤ W) {b' x : ℕ} (hx : x < W) : ∀ n,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc (Nat.shiftLeft (F b) (off b))) n).testBit
      (b' * W + x) = (decide (b' < n) && decide (c ≤ x) && (F b').testBit (x - c))
  | 0 => by
    change Nat.testBit 0 _ = _
    simp
  | n + 1 => by
    change (Nat.lor _ (Nat.shiftLeft (F n) (off n))).testBit _ = _
    rw [nlor, nshl, Nat.testBit_or, testBit_chunks hF hoff hcW hx n, Nat.testBit_shiftLeft, hoff]
    rcases Nat.lt_trichotomy b' n with h | rfl | h
    · have h1 : (b' + 1) * W ≤ n * W := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at h1
      rw [decide_eq_false (by omega : ¬ (b' * W + x ≥ c + n * W)), decide_eq_true h,
        decide_eq_true (by omega : b' < n + 1)]
      simp
    · rw [decide_eq_false (Nat.lt_irrefl _), decide_eq_true (Nat.lt_succ_self _), Bool.false_and,
        Bool.false_and, Bool.false_or, Bool.true_and]
      by_cases hc : c ≤ x
      · rw [decide_eq_true (by omega : b' * W + x ≥ c + b' * W), decide_eq_true hc, Bool.true_and,
          Bool.true_and]
        congr 1
        omega
      · rw [decide_eq_false (by omega : ¬ (b' * W + x ≥ c + b' * W)), decide_eq_false hc]
        rfl
    · have h1 : (n + 1) * W ≤ b' * W := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at h1
      rw [decide_eq_false (by omega : ¬ b' < n), decide_eq_false (by omega : ¬ b' < n + 1)]
      simp only [Bool.false_and, Bool.false_or]
      rw [bit_hi (hF n) (by omega)]
      simp

theorem chunks_lt {F off : ℕ → ℕ} {c L W : ℕ} (hF : ∀ b, F b < 2 ^ L) (hoff : ∀ b, off b = c + b * W)
    (hcW : c + L ≤ W) (hW : 0 < W) (n : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc (Nat.shiftLeft (F b) (off b))) n <
      2 ^ (n * W) := by
  refine Nat.lt_pow_two_of_testBit _ fun q hq => ?_
  have e := Nat.div_add_mod q W
  have hm := Nat.mod_lt q hW
  have hdiv : n ≤ q / W := (Nat.le_div_iff_mul_le hW).2 hq
  rw [← e, Nat.mul_comm, testBit_chunks hF hoff hcW hm, decide_eq_false (by omega)]
  rfl

theorem gat_compactN {o : ℕ} (ho : o + SA ≤ SX) :
    Gat SX SA (fun np X => compactN np o X) (fun x => o + x) (fun _ => false) where
  lt x hx := by omega
  bit np X b x hb hx := by
    have hF : ∀ b, Nat.land (Nat.shiftRight X (Nat.add o (Nat.mul b SX))) (ones SA) < 2 ^ SA :=
      fun b => by rw [nland, Benes.ones_eq]; exact Benes.land_ones_lt _ _
    have := testBit_chunks (F := fun b => Nat.land (Nat.shiftRight X (Nat.add o (Nat.mul b SX))) (ones SA))
      (off := fun b => Nat.mul b SA) (c := 0) (L := SA) (W := SA) hF (fun b => by simp [nmul])
      (by omega) hx np (b' := b)
    refine this.trans ?_
    rw [decide_eq_true hb, decide_eq_true (Nat.zero_le x), Nat.sub_zero, nland, nshr,
      Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, decide_eq_true hx]
    simp only [nadd, nmul, Bool.true_and, Bool.and_true, Bool.not_false]
    congr 1
    ring
  bd np X _ := by
    have hF : ∀ b, Nat.land (Nat.shiftRight X (Nat.add o (Nat.mul b SX))) (ones SA) < 2 ^ SA :=
      fun b => by rw [nland, Benes.ones_eq]; exact Benes.land_ones_lt _ _
    exact chunks_lt (F := fun b => Nat.land (Nat.shiftRight X (Nat.add o (Nat.mul b SX))) (ones SA))
      (off := fun b => Nat.mul b SA) (c := 0) hF (fun b => by simp [nmul]) (le_refl _)
      (by decide) np

theorem gat_expandN {o : ℕ} (ho : o + SA ≤ SX) :
    Gat SA SX (fun np X => expandN np o X) (fun x => (x - o) % SA)
      (fun x => !(decide (o ≤ x) && decide (x < o + SA))) where
  lt x _ := Nat.mod_lt _ (by decide)
  bit np X b x hb hx := by
    have hF : ∀ b, Nat.land (Nat.shiftRight X (Nat.mul b SA)) (ones SA) < 2 ^ SA :=
      fun b => by rw [nland, Benes.ones_eq]; exact Benes.land_ones_lt _ _
    have := testBit_chunks (F := fun b => Nat.land (Nat.shiftRight X (Nat.mul b SA)) (ones SA))
      (off := fun b => Nat.add o (Nat.mul b SX)) (c := o) (L := SA) (W := SX) hF
      (fun b => by simp [nmul, nadd]) ho hx np (b' := b)
    refine this.trans ?_
    rw [decide_eq_true hb, nland, nshr, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones]
    simp only [nmul, Bool.true_and]
    by_cases h1 : o ≤ x
    · by_cases h2 : x < o + SA
      · rw [decide_eq_true h1, decide_eq_true h2, decide_eq_true (by omega : x - o < SA),
          Nat.mod_eq_of_lt (by omega : x - o < SA)]
        simp
      · rw [decide_eq_true h1, decide_eq_false h2, decide_eq_false (by omega : ¬ x - o < SA)]
        simp
    · rw [decide_eq_false h1]
      simp
  bd np X _ := by
    have hF : ∀ b, Nat.land (Nat.shiftRight X (Nat.mul b SA)) (ones SA) < 2 ^ SA :=
      fun b => by rw [nland, Benes.ones_eq]; exact Benes.land_ones_lt _ _
    exact chunks_lt (F := fun b => Nat.land (Nat.shiftRight X (Nat.mul b SA)) (ones SA))
      (off := fun b => Nat.add o (Nat.mul b SX)) (c := o) hF (fun b => by simp [nmul, nadd]) ho
      (by decide) np

theorem testBit_pairBlocks (q : ℕ) :
    pairBlocks.testBit q = (decide (114688 ≤ q) && decide (q < 116736)) := by
  unfold pairBlocks
  rw [nshl, Nat.testBit_shiftLeft, testBit_ones]
  by_cases h : 114688 ≤ q
  · rw [decide_eq_true (by omega : q ≥ 114688), Bool.true_and, Bool.true_and]
    by_cases h2 : q < 116736
    · rw [decide_eq_true h2, decide_eq_true (by omega : q - 114688 < 2048)]
    · rw [decide_eq_false h2, decide_eq_false (by omega : ¬ q - 114688 < 2048)]
  · rw [decide_eq_false (by omega : ¬ q ≥ 114688), Bool.false_and, Bool.false_and]

theorem pairBlocks_lt : pairBlocks < 2 ^ SX :=
  lt_of_bits fun i hi => by
    rw [testBit_pairBlocks] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    have : SX = 131072 := rfl
    omega

theorem gat_clearPB :
    Gat SX SX (fun np X => Nat.land X (Nat.xor (mN SX np) (repN SX np pairBlocks))) id
      (fun x => pairBlocks.testBit x) where
  lt _ hx := hx
  bit np X b x hb hx := by
    have h1 : b * SX + x < np * SX := by
      have : (b + 1) * SX ≤ np * SX := Nat.mul_le_mul_right _ hb
      rw [Nat.succ_mul] at this
      omega
    rw [nland, nxor, Nat.testBit_and, Nat.testBit_xor, rep_bit (repN_rep pairBlocks_lt np) hb hx]
    unfold mN
    rw [testBit_ones, nmul, decide_eq_true h1, id]
    cases pairBlocks.testBit x <;> cases X.testBit (b * SX + x) <;> rfl
  bd np X hX := Nat.lt_of_le_of_lt Nat.and_le_left hX

theorem pg_cn5 {S K : ℕ} (hS : S = 2 ^ K) (hK : 5 ≤ K) {E : MonoE} (hE : monoNetsOK E = true) (R : ℕ) :
    ∃ π, PG S (fun np X => netRepN S np 5 (repLow S 5) R E.cn X) π := by
  unfold monoNetsOK at hE
  obtain ⟨h1, -⟩ := Benes.andB_true hE
  obtain ⟨h1, -⟩ := Benes.andB_true h1
  obtain ⟨h1, -⟩ := Benes.andB_true h1
  exact pg_netRepN hS hK h1 R

theorem nets_ok {E : MonoE} (hE : monoNetsOK E = true) :
    netOK 5 E.cn = true ∧ netOK 11 E.on = true ∧ netOK 10 E.qn = true ∧ netOK 12 E.wn = true ∧
      E.psw < 2 ^ SA ∧ E.sgX < 2 ^ SX ∧ E.sgW < 2 ^ SX ∧ E.sgA < 2 ^ SA := by
  unfold monoNetsOK at hE
  obtain ⟨h1, h2⟩ := Benes.andB_true hE
  obtain ⟨h1, h3⟩ := Benes.andB_true h1
  obtain ⟨a1, a2⟩ := Benes.andB_true h1
  obtain ⟨a3, a4⟩ := Benes.andB_true h3
  obtain ⟨-, h2⟩ := Benes.andB_true h2
  obtain ⟨h4, h5⟩ := Benes.andB_true h2
  obtain ⟨b1, b2⟩ := Benes.andB_true h4
  obtain ⟨b3, b4⟩ := Benes.andB_true h5
  simp only [Nat.blt_eq, nshl, Nat.one_shiftLeft] at b1 b2 b3 b4
  exact ⟨a1, a2, a3, a4, b1, b2, b3, b4⟩

@[expose] noncomputable def tauT (k : ℕ) : ℕ → ℕ :=
  Benes.swp (Nat.sub (Nat.shiftLeft 1 (Nat.add k 5)) (Nat.shiftLeft 1 k))
    (Nat.land (idPlane SA k) (clrN SA (Nat.add k 5)))

theorem pg_transpN : PG SA (fun np X => transpN np X) (preC tauT 5) :=
  (pg_preIt 5 (τ := tauT) (g := fun k np y => dsw (Nat.sub (Nat.shiftLeft 1 (Nat.add k 5))
        (Nat.shiftLeft 1 k)) (repN SA np (Nat.land (idPlane SA k) (clrN SA (Nat.add k 5)))) y)
      fun k hk => pg_dsw (validIn_bx (K := 10) (a := k) (b := Nat.add k 5)
        (by simp only [nadd]; omega) (by simp only [nadd]; omega))).congrF fun np X => by
    rw [← rec_pre1]
    rfl

theorem transp_pi : ∀ x < 1024, preC tauT 5 x = 32 * (x % 32) + x / 32 := by decide +kernel

theorem pg_amapN {E : MonoE} (hE : monoNetsOK E = true) :
    ∃ π, PG SA (fun np X => amapN np E.cn X) π := by
  obtain ⟨π1, h1⟩ := pg_netRepN SA_eq (by norm_num) (nets_ok hE).1 (ones SA)
  have hT' := pg_transpN
  exact ⟨_, (PG.comp (PG.comp (PG.comp h1 hT') h1) hT').congrF fun _ _ => rfl⟩

theorem pg_monoW {E : MonoE} (hE : monoNetsOK E = true) :
    ∃ π, PG SX (fun np X => monoW np E X) π := by
  obtain ⟨π1, h1⟩ := pg_netRepN SX_eq (by norm_num) (nets_ok hE).1 (ones SX)
  obtain ⟨π2, h2⟩ := pg_rotrN (lo := 0) (w := 17) (r := 5) SX_eq (by norm_num) (by norm_num) (ones SX)
  obtain ⟨π3, h3⟩ := pg_netRepN SX_eq (by norm_num) (nets_ok hE).2.2.2.1 (ones SX)
  obtain ⟨π4, h4⟩ := pg_rotrN (lo := 0) (w := 17) (r := 12) SX_eq (by norm_num) (by norm_num) (ones SX)
  exact ⟨_, (PG.comp (PG.comp (PG.comp h1 h2) h3) h4).congrF fun _ _ => rfl⟩

theorem gat_monoOdd {E : MonoE} (hE : monoNetsOK E = true) :
    ∃ π Z, Gat SX SX (fun np X => monoOdd np E X) π Z := by
  obtain ⟨_, h1⟩ := pg_netRepN (k := 5) SX_eq (by norm_num) (nets_ok hE).1 lo16
  obtain ⟨_, h2⟩ := pg_rotrN (lo := 0) (w := 16) (r := 5) SX_eq (by norm_num) (by norm_num) lo16
  obtain ⟨_, h3⟩ := pg_netRepN (k := 11) SX_eq (by norm_num) (nets_ok hE).2.1 lo16
  obtain ⟨_, h4⟩ := pg_rotrN (lo := 0) (w := 16) (r := 11) SX_eq (by norm_num) (by norm_num) lo16
  obtain ⟨_, h5⟩ := pg_rotrN (lo := 0) (w := 16) (r := 6) SX_eq (by norm_num) (by norm_num)
    (idPlane SX 16)
  obtain ⟨_, h6⟩ := pg_octSlots E
  obtain ⟨_, h7⟩ := pg_netRepN (k := 10) SX_eq (by norm_num) (nets_ok hE).2.2.1 (idPlane SX 16)
  obtain ⟨_, h8⟩ := pg_rotrN (lo := 0) (w := 16) (r := 10) SX_eq (by norm_num) (by norm_num)
    (idPlane SX 16)
  have P := PG.comp (PG.comp (PG.comp (PG.comp (PG.comp (PG.comp (PG.comp h1 h2) h3) h4) h5) h6) h7) h8
  exact ⟨_, _, (Gat.comp gat_clearPB P.g).congrF fun _ _ => rfl⟩

theorem upA_lt : upA < 2 ^ SA := by decide +kernel

theorem upA_tr : ∀ x < 1024, upA.testBit x = true → upA.testBit (32 * (x % 32) + x / 32) = false := by
  decide +kernel

theorem gat_monoPair {E : MonoE} (hE : monoNetsOK E = true) {o : ℕ} (ho : o + SA ≤ SX) :
    ∃ π Z, Gat SX SA (fun np X => monoPair np E o X) π Z := by
  have GP := Gat.comp (gat_compactN ho) (gat_mask upA_lt)
  have GT := Gat.comp GP pg_transpN.g
  have GU := Gat.union GP GT fun x hx => by
    simp only [Bool.or_false, Bool.false_or, Bool.not_eq_true']
    by_cases h : upA.testBit x = true
    · right
      rw [transp_pi x hx]
      simpa using upA_tr x hx h
    · left
      simpa using h
  obtain ⟨_, hA⟩ := pg_amapN hE
  exact ⟨_, _, (Gat.comp GU hA.g).congrF fun _ _ => rfl⟩

theorem gat_half {E : MonoE} (hE : monoNetsOK E = true) {o1 o2 o : ℕ} (h1 : o1 + SA ≤ SX)
    (h2 : o2 + SA ≤ SX) (ho : o + SA ≤ SX) {m : ℕ} (hm : m < 2 ^ SA) :
    ∃ π Z, Gat SX SX (fun np X => expandN np o (Nat.land (Nat.lor
        (Nat.land (monoPair np E o1 X) (repN SA np (Nat.xor (ones SA) m)))
        (Nat.land (monoPair np E o2 X) (repN SA np m))) (repN SA np upA))) π Z ∧
      ∀ x < SX, ¬ (o ≤ x ∧ x < o + SA) → Z x = true := by
  obtain ⟨_, _, G1⟩ := gat_monoPair hE h1
  obtain ⟨_, _, G2⟩ := gat_monoPair hE h2
  have hlt : Nat.xor (ones SA) m < 2 ^ SA := Nat.xor_lt_two_pow (ones_lt SA) hm
  have M1 := Gat.comp G1 (gat_mask hlt)
  have M2 := Gat.comp G2 (gat_mask hm)
  have U := Gat.union M1 M2 fun x hx => by
    rw [nxor, Nat.testBit_xor, testBit_ones, decide_eq_true hx]
    cases m.testBit x <;> simp
  have W := Gat.comp (Gat.comp U (gat_mask upA_lt)) (gat_expandN ho)
  refine ⟨_, _, W.congrF fun _ _ => rfl, fun x _ h => ?_⟩
  have e : (decide (o ≤ x) && decide (x < o + SA)) = false := by
    by_cases h' : o ≤ x
    · rw [decide_eq_true h', decide_eq_false fun h'' => h ⟨h', h''⟩]
      rfl
    · rw [decide_eq_false h']
      rfl
  simp [e]

theorem gat_pairs {E : MonoE} (hE : monoNetsOK E = true) :
    ∃ π Z, Gat SX SX (fun np X => pairsBack np E.psw (monoPair np E 114688 X)
        (monoPair np E 115712 X)) π Z ∧ ∀ x < SX, pairBlocks.testBit x = false → Z x = true := by
  have hp := (nets_ok hE).2.2.2.2.1
  have hSX : SX = 131072 := rfl
  have hSA : SA = 1024 := rfl
  obtain ⟨_, _, Ga, ha⟩ := gat_half (o1 := 114688) (o2 := 115712) (o := 114688) hE (by omega)
    (by omega) (by omega) hp
  obtain ⟨_, _, Gb, hb⟩ := gat_half (o1 := 115712) (o2 := 114688) (o := 115712) hE (by omega)
    (by omega) (by omega) hp
  have U := Gat.union Ga Gb fun x hx => by
    by_cases h : 114688 ≤ x ∧ x < 114688 + SA
    · exact Or.inr (hb x hx (by omega))
    · exact Or.inl (ha x hx h)
  refine ⟨_, _, U.congrF fun _ _ => rfl, fun x hx h => ?_⟩
  rw [testBit_pairBlocks] at h
  have h' : ¬ (114688 ≤ x ∧ x < 116736) := by
    intro h''
    rw [decide_eq_true h''.1, decide_eq_true h''.2] at h
    exact absurd h (by decide)
  simp only [Bool.and_eq_true]
  exact ⟨ha x hx (by omega), hb x hx (by omega)⟩

theorem gat_moveX {E : MonoE} (hE : monoNetsOK E = true) (hP : monoPadOK E = true) :
    ∃ π Z, Gat SX SX (fun np X => monoMoveX np E X) π Z := by
  obtain ⟨π1, Z1, G1⟩ := gat_monoOdd hE
  obtain ⟨_, _, G2, h2⟩ := gat_pairs hE
  have hpad : ∀ x < SX, pairBlocks.testBit x = true → Z1 x = true := by
    intro x hx hb
    have h0 : Nat.land (monoOdd 1 E (ones SX)) pairBlocks = 0 := by
      unfold monoPadOK at hP
      rwa [Nat.beq_eq] at hP
    have h3 := congrArg (fun y => y.testBit x) h0
    simp only [nland, Nat.testBit_and, hb, Bool.and_true, Nat.zero_testBit] at h3
    have h4 := G1.bit 1 (ones SX) 0 x (by decide) hx
    rw [Nat.zero_mul, Nat.zero_add, Nat.zero_add, h3, testBit_ones, decide_eq_true (G1.lt x hx),
      Bool.and_true] at h4
    cases h5 : Z1 x
    · rw [h5] at h4
      exact absurd h4 (by decide)
    · rfl
  have U := Gat.union G1 G2 fun x hx => by
    cases hb : pairBlocks.testBit x
    · exact Or.inr (h2 x hx hb)
    · exact Or.inl (hpad x hx hb)
  exact ⟨_, _, U.congrF fun _ _ => rfl⟩

theorem res_gat {S T : ℕ} {f : ℕ → ℕ → ℕ} {π : ℕ → ℕ} {Z : ℕ → Bool} (hG : Gat S T f π Z)
    (np X : ℕ) {x : ℕ} (hx : x < T) :
    resPN np T (f np X) x = if Z x = true then 0 else resPN np S X (π x) := by
  unfold resPN
  split
  · next h =>
    have : ∀ b ∈ Finset.range np, 2 ^ b * (f np X / 2 ^ (b * T + x) % 2) = 0 := by
      intro b hb
      rw [← Nat.toNat_testBit, hG.bit np X b x (Finset.mem_range.1 hb) hx, h]
      simp
    have hs : ∑ b ∈ Finset.range np, 2 ^ b * (f np X / 2 ^ (b * T + x) % 2) = 0 :=
      Finset.sum_eq_zero this
    rw [hs]
    simp
  · next h =>
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [← Nat.toNat_testBit, ← Nat.toNat_testBit, hG.bit np X b x (Finset.mem_range.1 hb) hx]
    simp [h]

@[expose] noncomputable def pv (S K p : ℕ) : ℕ := packN (fun b => K.testBit (b * S + p)) 12

theorem holds_pv (S K p : ℕ) : Holds 12 S K p (pv S K p) := fun b hb => by
  unfold pv
  rw [testBit_packN, decide_eq_true hb, Bool.true_and]

theorem pv_lt (S K p : ℕ) : pv S K p < 4096 := packN_lt _ 12

theorem eq12 {x y : ℕ} (hx : x < 4096) (hy : y < 4096) (h : ∀ b < 12, x.testBit b = y.testBit b) :
    x = y :=
  Nat.eq_of_testBit_eq fun b => by
    by_cases hb : b < 12
    · exact h b hb
    · rw [bit_hi (n := 12) hx (by omega), bit_hi (n := 12) hy (by omega)]

theorem pv_of_holds {S K p x : ℕ} (h : Holds 12 S K p x) (hx : x < 4096) : pv S K p = x :=
  eq12 (pv_lt S K p) hx fun b hb => by rw [← holds_pv S K p b hb, h b hb]

theorem pv_key {F : Fix} (hK : KeyBind F) (hG : KeysGood) {q : ℕ} (hq : q < 98280) :
    pv SX F.keyA (xposK q) = (keyQ q).1 ∧ pv SX F.keyD (xposK q) = (keyQ q).2 :=
  ⟨pv_of_holds (fun b hb => hK.ka q hq b hb) (hG.1 q hq).1,
    pv_of_holds (fun b hb => hK.kd q hq b hb) (hG.1 q hq).2⟩

theorem pv_pad {F : Fix} (hK : KeyBind F) {p : ℕ} (hp : p < SX) (hno : ∀ q < 98280, xposK q ≠ p) :
    pv SX F.keyA p = 0 ∧ pv SX F.keyD p = 0 :=
  ⟨pv_of_holds (fun b hb => by rw [hK.pa p hp hno b hb, Nat.zero_testBit]) (by decide),
    pv_of_holds (fun b hb => by rw [hK.pd p hp hno b hb, Nat.zero_testBit]) (by decide)⟩

theorem K24_bit {F : Fix} (hK : KeyBind F) {x b : ℕ} (hx : x < SX) :
    (Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul 12 SX))).testBit (b * SX + x) =
      if b < 12 then (pv SX F.keyA x).testBit b else (pv SX F.keyD x).testBit (b - 12) := by
  rw [testBit_split12 hK.la hx]
  split_ifs with hb
  · exact holds_pv SX F.keyA x b hb
  · by_cases hb' : b - 12 < 12
    · exact holds_pv SX F.keyD x (b - 12) hb'
    · rw [bit_hi (n := 12) (pv_lt _ _ _) (by omega)]
      have : 12 * SX ≤ (b - 12) * SX := Nat.mul_le_mul_right _ (by omega)
      exact bit_hi hK.ld (by omega)

variable {M : ℕ} {h : ZMod M}

theorem sgnI_mul (b : Bool) (x : ZMod M) : ((sgnI b : ℤ) : ZMod M) * x = if b then -x else x := by
  cases b <;> simp [sgnI]

theorem two_hN' {np : ℕ} (hnp : 1 ≤ np) : 2 * hN np = 1 := by
  unfold hN
  rw [← pow_succ', Nat.sub_add_cancel hnp]
  have h0 : ((2 ^ np - 1 : ℕ) : ZMod (2 ^ np - 1)) = 0 := ZMod.natCast_self _
  rw [Nat.cast_sub Nat.one_le_two_pow] at h0
  push_cast at h0
  exact sub_eq_zero.mp h0

theorem resN_eq (n : ℕ) (w : Native.DVec) (k : ℕ) : resN n w k = resM (hN n) w k := rfl

theorem moveX_sound {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {F : Fix} (hK : KeyBind F)
    (hG : KeysGood) {E : MonoE} (hNets : monoNetsOK E = true) (hPad : monoPadOK E = true)
    (img : ℕ → ℕ → ℕ × ℕ) (himg : ∀ a d, (img a d).1 < 4096 ∧ (img a d).2 < 4096)
    (h0 : img 0 0 = (0, 0)) {L : ℕ}
    (hL : ∀ p < SX, ∀ b < 24, L.testBit (b * SX + p) =
      if b < 12 then (img (pv SX F.keyA p) (pv SX F.keyD p)).1.testBit b
      else (img (pv SX F.keyA p) (pv SX F.keyD p)).2.testBit (b - 12))
    (hchk : monoMoveX 24 E L = Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul 12 SX)))
    (sg : ℕ → ℕ → Bool) (hsg : ∀ q < 98280, E.sgX.testBit (xposK q) = sg (keyQ q).1 (keyQ q).2)
    {g : Native.GD}
    (hxT : ∀ p < 98280, g.xT (Native.mkCtx ()) p =
      [((Native.mkCtx ()).find (img (keyQ p).1 (keyQ p).2).1 (img (keyQ p).1 (keyQ p).2).2,
        sgnI (sg (keyQ p).1 (keyQ p).2))])
    {v : Native.DVec} {X : ℕ}
    (hX1 : ∀ q < 98280, resPN n SX X (xposK q) = resN n v (300 + q))
    (hX2 : ∀ p < SX, (∀ q < 98280, xposK q ≠ p) → resPN n SX X p = 0) (hX3 : X < 2 ^ (n * SX)) :
    (∀ q < 98280, resPN n SX (monoMoveX n E (negMN SX n E.sgX X)) (xposK q) =
      resN n (Native.applyGD (Native.mkCtx ()) g v) (300 + q)) ∧
    (∀ p < SX, (∀ q < 98280, xposK q ≠ p) → resPN n SX (monoMoveX n E (negMN SX n E.sgX X)) p = 0) ∧
      monoMoveX n E (negMN SX n E.sgX X) < 2 ^ (n * SX) := by
  obtain ⟨π, Z, G⟩ := gat_moveX hNets hPad
  have hO := opsN_law hn hlg
  have hsgl := (nets_ok hNets).2.2.2.2.2.1
  have h2 := two_hN' (np := n) (by omega)
  have eneg : negMN SX n E.sgX X = (opsN n lg).neg SX E.sgX X := rfl
  have hneg : ∀ p < SX, resPN n SX (negMN SX n E.sgX X) p =
      if E.sgX.testBit p then -resPN n SX X p else resPN n SX X p := fun p hp => by
    rw [eneg]
    exact hO.neg_res hsgl hX3 hp
  have hc : ∀ x < SX, ∀ b < 24,
      (if b < 12 then (pv SX F.keyA x).testBit b else (pv SX F.keyD x).testBit (b - 12)) =
        (!Z x && (if b < 12 then (img (pv SX F.keyA (π x)) (pv SX F.keyD (π x))).1.testBit b
          else (img (pv SX F.keyA (π x)) (pv SX F.keyD (π x))).2.testBit (b - 12))) := by
    intro x hx b hb
    rw [← K24_bit hK hx, ← hchk, G.bit 24 L b x hb hx, hL _ (G.lt x hx) b hb]
  have hlab : ∀ x < SX, Z x = false →
      img (pv SX F.keyA (π x)) (pv SX F.keyD (π x)) = (pv SX F.keyA x, pv SX F.keyD x) := by
    intro x hx hz
    refine Prod.ext (eq12 (himg _ _).1 (pv_lt _ _ _) fun b hb => ?_)
      (eq12 (himg _ _).2 (pv_lt _ _ _) fun b hb => ?_)
    · have := hc x hx b (by omega)
      rw [if_pos hb, if_pos hb, hz, Bool.not_false, Bool.true_and] at this
      exact this.symm
    · have := hc x hx (b + 12) (by omega)
      rw [if_neg (by omega), if_neg (by omega), hz, Bool.not_false, Bool.true_and,
        Nat.add_sub_cancel] at this
      exact this.symm
  have hz0 : ∀ x < SX, Z x = true → pv SX F.keyA x = 0 ∧ pv SX F.keyD x = 0 := by
    intro x hx hz
    refine ⟨eq12 (pv_lt _ _ _) (by decide) fun b hb => ?_, eq12 (pv_lt _ _ _) (by decide) fun b hb => ?_⟩
    · have := hc x hx b (by omega)
      rw [if_pos hb, if_pos hb, hz, Bool.not_true, Bool.false_and] at this
      rw [this, Nat.zero_testBit]
    · have := hc x hx (b + 12) (by omega)
      rw [if_neg (by omega), if_neg (by omega), hz, Bool.not_true, Bool.false_and,
        Nat.add_sub_cancel] at this
      rw [this, Nat.zero_testBit]
  have hkey : ∀ q < 98280, Z (xposK q) = false ∧ ∃ c < 98280, xposK c = π (xposK q) ∧
      img (keyQ c).1 (keyQ c).2 = keyQ q := by
    intro q hq
    have hxq := InitAux.xposK_lt' hq
    obtain ⟨ka, kd⟩ := pv_key hK hG hq
    have hz : Z (xposK q) = false := by
      cases hz : Z (xposK q)
      · rfl
      · obtain ⟨h1, h2⟩ := hz0 _ hxq hz
        exact absurd (Prod.ext (ka.symm.trans h1) (kd.symm.trans h2)) (keyQ_ne_zero hq)
    refine ⟨hz, ?_⟩
    have hl := hlab _ hxq hz
    rw [ka, kd] at hl
    by_contra hno
    have hno' : ∀ c < 98280, xposK c ≠ π (xposK q) := fun c hc e => by
      by_cases hk : img (keyQ c).1 (keyQ c).2 = keyQ q
      · exact hno ⟨c, hc, e, hk⟩
      · apply hk
        obtain ⟨ka', kd'⟩ := pv_key hK hG hc
        rw [← ka', ← kd', e, hl]
    obtain ⟨p1, p2⟩ := pv_pad hK (G.lt _ hxq) hno'
    rw [p1, p2, h0] at hl
    exact keyQ_ne_zero hq hl.symm
  choose! τ hτ using fun q (hq : q < 98280) => (hkey q hq).2
  have hτlt : ∀ q < 98280, τ q < 98280 := fun q hq => (hτ q hq).1
  have hσ : ∀ q < 98280, (Native.mkCtx ()).find (img (keyQ (τ q)).1 (keyQ (τ q)).2).1
      (img (keyQ (τ q)).1 (keyQ (τ q)).2).2 = q := fun q hq => by
    rw [(hτ q hq).2.2]
    exact mkCtx_find hG hq
  have hτinj : ∀ q < 98280, ∀ q' < 98280, τ q = τ q' → q = q' := fun q hq q' hq' e => by
    rw [← hσ q hq, ← hσ q' hq', e]
  have hτsurj := surj_of_inj hτlt hτinj
  have hσinj : ∀ p < 98280, ∀ p' < 98280,
      (Native.mkCtx ()).find (img (keyQ p).1 (keyQ p).2).1 (img (keyQ p).1 (keyQ p).2).2 =
        (Native.mkCtx ()).find (img (keyQ p').1 (keyQ p').2).1 (img (keyQ p').1 (keyQ p').2).2 →
      p = p' := fun p hp p' hp' e => by
    obtain ⟨q, hq, rfl⟩ := hτsurj p hp
    obtain ⟨q', hq', rfl⟩ := hτsurj p' hp'
    rw [hσ q hq, hσ q' hq'] at e
    rw [e]
  refine ⟨fun q hq => ?_, fun p hp hno => ?_, G.bd n _ (eneg ▸ hO.neg_bd hsgl hX3)⟩
  · have hxq := InitAux.xposK_lt' hq
    rw [res_gat G n _ hxq, if_neg (by rw [(hkey q hq).1]; decide), ← (hτ q hq).2.1,
      hneg _ (InitAux.xposK_lt' (hτlt q hq)), hX1 _ (hτlt q hq), hsg _ (hτlt q hq), resN_eq,
      resN_eq, applyGD_resX h2 _ _ _ hq, sum_scat_single hxT hσinj]
    have hex : ∃ p < 98280, (Native.mkCtx ()).find (img (keyQ p).1 (keyQ p).2).1
        (img (keyQ p).1 (keyQ p).2).2 = q := ⟨τ q, hτlt q hq, hσ q hq⟩
    rw [dite_eq_left hex]
    have hc : hex.choose = τ q := hσinj _ hex.choose_spec.1 _ (hτlt q hq)
      (hex.choose_spec.2.trans (hσ q hq).symm)
    rw [hc, sgnI_mul]
  · rw [res_gat G n _ hp]
    split_ifs with hz
    · rfl
    · rw [Bool.not_eq_true] at hz
      have hpx := G.lt p hp
      rw [hneg _ hpx]
      by_cases hv : ∃ c < 98280, xposK c = π p
      · exfalso
        obtain ⟨c, hc, e⟩ := hv
        obtain ⟨q, hq, rfl⟩ := hτsurj c hc
        have hl := hlab p hp hz
        obtain ⟨ka', kd'⟩ := pv_key hK hG hc
        obtain ⟨p1, p2⟩ := pv_pad hK hp hno
        rw [← e, ka', kd', (hτ q hq).2.2, p1, p2] at hl
        exact keyQ_ne_zero hq hl
      · have hno' : ∀ c < 98280, xposK c ≠ π p := fun c hc e => hv ⟨c, hc, e⟩
        rw [hX2 _ hpx hno']
        simp

theorem labels_pi {S k : ℕ} (hS : S = 2 ^ k) {f : ℕ → ℕ → ℕ} {π : ℕ → ℕ} (hP : PG S f π)
    {Mk LL : ℕ} (hM : Mk < 2 ^ S) (nw : ℕ → ℕ)
    (hchk : eqOn S k Mk (f k LL) (idP k) = true)
    (hin : ∀ p < S, Mk.testBit p = true → Holds k S LL p (nw p))
    (hout : ∀ p < S, Mk.testBit p = false → Holds k S LL p p)
    (hnw : ∀ p < S, Mk.testBit p = true → nw p < S ∧ Mk.testBit (nw p) = true) :
    (∀ x < S, Mk.testBit x = true → Mk.testBit (π x) = true ∧ nw (π x) = x) ∧
      ((∀ p < S, ∀ p' < S, Mk.testBit p = true → Mk.testBit p' = true → nw p = nw p' → p = p') →
        ∀ x < S, Mk.testBit x = false → Mk.testBit (π x) = false) := by
  have hc : f k LL &&& repN S k Mk = idP k &&& repN S k Mk := by
    unfold eqOn at hchk
    rwa [Nat.beq_eq] at hchk
  have hR := repN_rep hM k
  have hsrc : ∀ x < S, Mk.testBit x = true → Holds k S LL (π x) x := by
    intro x hx hm b hb
    have := congrArg (fun y => y.testBit (b * S + x)) hc
    simp only [Nat.testBit_and, rep_bit hR hb hx, hm, Bool.and_true] at this
    have hb' := hP.g.bit k LL b x hb hx
    rw [Bool.not_false, Bool.true_and] at hb'
    rw [← hb', this]
    subst hS
    exact testBit_idP hb hx
  have hS' : S = 2 ^ k := hS
  have part1 : ∀ x < S, Mk.testBit x = true → Mk.testBit (π x) = true ∧ nw (π x) = x := by
    intro x hx hm
    have hpx := hP.g.lt x hx
    have h1 := hsrc x hx hm
    cases hmp : Mk.testBit (π x)
    · have := holds_eq h1 (hout _ hpx hmp) (by rw [← hS']; exact hx) (by rw [← hS']; exact hpx)
      rw [← this, hm] at hmp
      exact absurd hmp (by decide)
    · refine ⟨rfl, holds_eq (hin _ hpx hmp) h1 ?_ (by rw [← hS']; exact hx)⟩
      rw [← hS']
      exact (hnw _ hpx hmp).1
  refine ⟨part1, fun hinj x hx hm => ?_⟩
  have hpx := hP.g.lt x hx
  cases hmp : Mk.testBit (π x)
  · rfl
  · exfalso
    obtain ⟨hy, hmy⟩ := hnw _ hpx hmp
    obtain ⟨h1, h2⟩ := part1 _ hy hmy
    have := hinj _ (hP.g.lt _ hy) _ hpx h1 hmp h2
    have := hP.inj _ hy _ hx this
    rw [← this, hmy] at hm
    exact absurd hm (by decide)

theorem monoRows_get (rm : Bool → ℕ → Bool × Bool × ℕ) {r : ℕ} (hr : r < 4096) :
    (Native.monoRows rm)[r]! = [(Native.rowIdx (rm (Native.rowEta r) (Native.rowC r)).2.1
      (rm (Native.rowEta r) (Native.rowC r)).2.2, sgnI (rm (Native.rowEta r) (Native.rowC r)).1)] := by
  unfold Native.monoRows
  rw [getElem!_pos _ r (by simp; omega)]
  simp

structure MonoG (g : Native.GD) (col : ℕ → ℕ) (cs : ℕ → Bool) : Prop where
  lt : ∀ c < 24, col c < 24
  inj : ∀ c < 24, ∀ c' < 24, col c = col c' → c = c'
  get : ∀ j < 24, ∀ c < 24, g.G[j * 24 + c]! = if col j = c then sgnI (cs j) else 0

theorem MonoG.sum {g : Native.GD} {col : ℕ → ℕ} {cs : ℕ → Bool} (hg : MonoG g col cs) {k0 : ℕ}
    (hk0 : k0 < 24) (f : ℕ → ZMod M) :
    ∑ k ∈ Finset.range 24, ((g.G[k * 24 + col k0]! : ℤ) : ZMod M) * f k =
      ((sgnI (cs k0) : ℤ) : ZMod M) * f k0 := by
  rw [Finset.sum_eq_single k0]
  · rw [hg.get k0 hk0 _ (hg.lt k0 hk0), if_pos rfl]
  · intro j hj hne
    rw [hg.get j (Finset.mem_range.1 hj) _ (hg.lt k0 hk0),
      if_neg fun e => hne (hg.inj _ (Finset.mem_range.1 hj) _ hk0 e)]
    simp
  · intro hn
    exact absurd (Finset.mem_range.2 hk0) hn

theorem MonoG.surj {g : Native.GD} {col : ℕ → ℕ} {cs : ℕ → Bool} (hg : MonoG g col cs) :
    ∀ j < 24, ∃ i < 24, col i = j := surj_of_inj hg.lt hg.inj

theorem native_W (h2 : 2 * h = 1) {g : Native.GD} {rm : Bool → ℕ → Bool × Bool × ℕ}
    (hl : g.latS = 0) (hr : g.rowS = 0) (hrow : g.rowT = Native.monoRows rm)
    {col : ℕ → ℕ} {cs : ℕ → Bool} (hg : MonoG g col cs) {rowNew : ℕ → ℕ}
    (hrn : ∀ r < 4096, rowNew r = Native.rowIdx (rm (Native.rowEta r) (Native.rowC r)).2.1
      (rm (Native.rowEta r) (Native.rowC r)).2.2)
    (hrlt : ∀ r < 4096, rowNew r < 4096)
    (hrinj : ∀ r < 4096, ∀ r' < 4096, rowNew r = rowNew r' → r = r')
    (v : Native.DVec) {r c : ℕ} (hr4 : r < 4096) (hc : c < 24) :
    resM h (Native.applyGD (Native.mkCtx ()) g v) (98580 + 24 * rowNew r + col c) =
      ((sgnI (rm (Native.rowEta r) (Native.rowC r)).1 : ℤ) : ZMod M) *
        (((sgnI (cs c) : ℤ) : ZMod M) * resM h v (98580 + 24 * r + c)) := by
  have hcc := hg.lt c hc
  have hk : 24 * rowNew r + col c < 98304 := by have := hrlt r hr4; omega
  rw [Nat.add_assoc, applyGD_resW h2 _ _ _ hk, hl, hr, Nat.add_zero, pow_zero, one_mul]
  have hT : ∀ p < 98304, g.wT p = [(rowNew (p / 24) * 24 + p % 24,
      sgnI (rm (Native.rowEta (p / 24)) (Native.rowC (p / 24))).1)] := by
    intro p hp
    unfold Native.GD.wT
    rw [hrow, monoRows_get _ (by omega), hrn _ (by omega)]
    rfl
  have hinj : ∀ p < 98304, ∀ p' < 98304, rowNew (p / 24) * 24 + p % 24 =
      rowNew (p' / 24) * 24 + p' % 24 → p = p' := by
    intro p hp p' hp' e
    have h1 : p % 24 = p' % 24 := by omega
    have h3 : rowNew (p / 24) = rowNew (p' / 24) := by omega
    have := hrinj _ (by omega) _ (by omega) h3
    omega
  rw [sum_scat_single hT hinj]
  have hex : ∃ p < 98304, rowNew (p / 24) * 24 + p % 24 = 24 * rowNew r + col c :=
    ⟨24 * r + col c, by omega, by
      rw [show (24 * r + col c) / 24 = r by omega, show (24 * r + col c) % 24 = col c by omega]
      ring⟩
  rw [dite_eq_left hex]
  obtain ⟨h1, h3⟩ := hex.choose_spec
  have hch : hex.choose = 24 * r + col c := hinj _ h1 _ (by omega) (by
    rw [h3, show (24 * r + col c) / 24 = r by omega, show (24 * r + col c) % 24 = col c by omega]
    ring)
  rw [hch, show (24 * r + col c) / 24 = r by omega, show (24 * r + col c) % 24 = col c by omega,
    hg.sum hc (fun j => resM h v (98580 + r * 24 + j)), Nat.mul_comm r 24]

theorem native_A (h2 : 2 * h = 1) {g : Native.GD} (hl : g.latS = 0) {col : ℕ → ℕ} {cs : ℕ → Bool}
    (hg : MonoG g col cs) (v : Native.DVec) {i j : ℕ} (hi : i < 24) (hj : j < 24) :
    resM h (Native.applyGD (Native.mkCtx ()) g v) (Native.aIdx (col i) (col j)) =
      ((sgnI (cs i) : ℤ) : ZMod M) * (((sgnI (cs j) : ℤ) : ZMod M) * resM h v (Native.aIdx i j)) := by
  have hci := hg.lt i hi
  have hcj := hg.lt j hj
  rw [applyGD_resA h2 _ _ _ (InitAux.aIdx_lt _ hci _ hcj), ListAux.aPos_aIdx _ hci _ hcj, hl,
    Nat.mul_zero, pow_zero, one_mul]
  have e : ∀ k, ∑ l ∈ Finset.range 24, ((g.G[k * 24 + min (col i) (col j)]! : ℤ) : ZMod M) *
      ((g.G[l * 24 + max (col i) (col j)]! : ℤ) : ZMod M) * resM h v (Native.aIdx k l) =
      ((g.G[k * 24 + min (col i) (col j)]! : ℤ) : ZMod M) * ∑ l ∈ Finset.range 24,
        ((g.G[l * 24 + max (col i) (col j)]! : ℤ) : ZMod M) * resM h v (Native.aIdx k l) := by
    intro k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [e]
  rcases le_total (col i) (col j) with hij | hij
  · rw [min_eq_left hij, max_eq_right hij, hg.sum hi, hg.sum hj]
  · rw [min_eq_right hij, max_eq_left hij, hg.sum hj, hg.sum hi,
      ListAux.aIdx_comm j hj i hi]
    ring

theorem sgn_sgn (a b : Bool) (x : ZMod M) :
    ((sgnI a : ℤ) : ZMod M) * (((sgnI b : ℤ) : ZMod M) * x) = if (a ^^ b) then -x else x := by
  cases a <;> cases b <;> simp [sgnI]

theorem moveW_sound {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {E : MonoE}
    (hNets : monoNetsOK E = true) {π : ℕ → ℕ} (hP : PG SX (fun np X => monoW np E X) π)
    {g : Native.GD} {rm : Bool → ℕ → Bool × Bool × ℕ}
    (hl : g.latS = 0) (hr : g.rowS = 0) (hrow : g.rowT = Native.monoRows rm)
    {col : ℕ → ℕ} {cs : ℕ → Bool} (hg : MonoG g col cs) {rowNew : ℕ → ℕ}
    (hrn : ∀ r < 4096, rowNew r = Native.rowIdx (rm (Native.rowEta r) (Native.rowC r)).2.1
      (rm (Native.rowEta r) (Native.rowC r)).2.2)
    (hrlt : ∀ r < 4096, rowNew r < 4096)
    (hrinj : ∀ r < 4096, ∀ r' < 4096, rowNew r = rowNew r' → r = r')
    (hπ : ∀ r < 4096, ∀ c < 24, π (32 * rowNew r + col c) = 32 * r + c)
    (hpad : ∀ x < SX, 24 ≤ x % 32 → 24 ≤ π x % 32)
    (hsg : ∀ r < 4096, ∀ c < 24, E.sgW.testBit (32 * r + c) =
      ((rm (Native.rowEta r) (Native.rowC r)).1 ^^ cs c))
    {v : Native.DVec} {W : ℕ}
    (hW1 : ∀ r < 4096, ∀ j < 24, resPN n SX W (32 * r + j) = resN n v (98580 + 24 * r + j))
    (hW2 : ∀ p < SX, 24 ≤ p % 32 → resPN n SX W p = 0) (hW3 : W < 2 ^ (n * SX)) :
    (∀ r < 4096, ∀ j < 24, resPN n SX (monoW n E (negMN SX n E.sgW W)) (32 * r + j) =
      resN n (Native.applyGD (Native.mkCtx ()) g v) (98580 + 24 * r + j)) ∧
    (∀ p < SX, 24 ≤ p % 32 → resPN n SX (monoW n E (negMN SX n E.sgW W)) p = 0) ∧
      monoW n E (negMN SX n E.sgW W) < 2 ^ (n * SX) := by
  have hO := opsN_law hn hlg
  have hsgl := (nets_ok hNets).2.2.2.2.2.2.1
  have h2 := two_hN' (np := n) (by omega)
  have hSX : SX = 131072 := rfl
  have eneg : negMN SX n E.sgW W = (opsN n lg).neg SX E.sgW W := rfl
  have hneg : ∀ p < SX, resPN n SX (negMN SX n E.sgW W) p =
      if E.sgW.testBit p then -resPN n SX W p else resPN n SX W p := fun p hp => by
    rw [eneg]
    exact hO.neg_res hsgl hW3 hp
  have hrs := surj_of_inj hrlt hrinj
  refine ⟨fun r' hr' j' hj' => ?_, fun p hp hpm => ?_, hP.g.bd n _ (eneg ▸ hO.neg_bd hsgl hW3)⟩
  · obtain ⟨r, hr4, rfl⟩ := hrs r' hr'
    obtain ⟨c, hc, rfl⟩ := hg.surj j' hj'
    have hx : 32 * rowNew r + col c < SX := by have := hrlt r hr4; have := hg.lt c hc; omega
    rw [res_gat hP.g n _ hx, if_neg (by decide), hπ r hr4 c hc, hneg _ (by omega), hW1 r hr4 c hc,
      hsg r hr4 c hc, resN_eq, resN_eq, native_W h2 hl hr hrow hg hrn hrlt hrinj v hr4 hc, sgn_sgn]
  · rw [res_gat hP.g n _ hp, if_neg (by decide), hneg _ (hP.g.lt p hp),
      hW2 _ (hP.g.lt p hp) (hpad p hp hpm)]
    simp

theorem moveA_sound {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {E : MonoE}
    (hNets : monoNetsOK E = true) {π : ℕ → ℕ} (hP : PG SA (fun np X => amapN np E.cn X) π)
    {g : Native.GD} (hl : g.latS = 0) {col : ℕ → ℕ} {cs : ℕ → Bool} (hg : MonoG g col cs)
    (hπ : ∀ i < 24, ∀ j < 24, π (32 * col i + col j) = 32 * i + j)
    (hpad : ∀ x < SA, (24 ≤ x % 32 ∨ 24 ≤ x / 32) → (24 ≤ π x % 32 ∨ 24 ≤ π x / 32))
    (hsg : ∀ i < 24, ∀ j < 24, E.sgA.testBit (32 * i + j) = (cs i ^^ cs j))
    {v : Native.DVec} {A : ℕ}
    (hA1 : ∀ i < 24, ∀ j < 24, resPN n SA A (32 * i + j) = resN n v (Native.aIdx i j))
    (hA2 : ∀ p < SA, (24 ≤ p % 32 ∨ 24 ≤ p / 32) → resPN n SA A p = 0) (hA3 : A < 2 ^ (n * SA)) :
    (∀ i < 24, ∀ j < 24, resPN n SA (amapN n E.cn (negMN SA n E.sgA A)) (32 * i + j) =
      resN n (Native.applyGD (Native.mkCtx ()) g v) (Native.aIdx i j)) ∧
    (∀ p < SA, (24 ≤ p % 32 ∨ 24 ≤ p / 32) → resPN n SA (amapN n E.cn (negMN SA n E.sgA A)) p = 0) ∧
      amapN n E.cn (negMN SA n E.sgA A) < 2 ^ (n * SA) := by
  have hO := opsN_law hn hlg
  have hsgl := (nets_ok hNets).2.2.2.2.2.2.2
  have h2 := two_hN' (np := n) (by omega)
  have eneg : negMN SA n E.sgA A = (opsN n lg).neg SA E.sgA A := rfl
  have hneg : ∀ p < SA, resPN n SA (negMN SA n E.sgA A) p =
      if E.sgA.testBit p then -resPN n SA A p else resPN n SA A p := fun p hp => by
    rw [eneg]
    exact hO.neg_res hsgl hA3 hp
  have hSA : SA = 1024 := rfl
  refine ⟨fun i' hi' j' hj' => ?_, fun p hp hpm => ?_, hP.g.bd n _ (eneg ▸ hO.neg_bd hsgl hA3)⟩
  · obtain ⟨i, hi, rfl⟩ := hg.surj i' hi'
    obtain ⟨j, hj, rfl⟩ := hg.surj j' hj'
    have hx : 32 * col i + col j < SA := by have := hg.lt i hi; have := hg.lt j hj; omega
    rw [res_gat hP.g n _ hx, if_neg (by decide), hπ i hi j hj, hneg _ (by omega), hA1 i hi j hj,
      hsg i hi j hj, resN_eq, resN_eq, native_A h2 hl hg v hi hj, sgn_sgn]
  · rw [res_gat hP.g n _ hp, if_neg (by decide), hneg _ (hP.g.lt p hp),
      hA2 _ (hP.g.lt p hp) (hpad p hp hpm)]
    simp

theorem permCT_nat {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) (a : ℕ) : permCT P a = permCN arr a := by
  rw [Trace6091.permCT_eq hA.pe, ← CFSG.Monster.B.Rep4371.native_permCN]

theorem permDT_nat {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) (d : ℕ) : permDT P d = permDN arr d := by
  rw [Trace6091.permDT_eq hA.pe, ← CFSG.Monster.B.Rep4371.native_permDN]

theorem holds_permC {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) {S X p x : ℕ} (hp : p < S)
    (hX : Holds 12 S X p x) : Holds 12 S (plin S (basisImg (permCT P)) X) p (permCN arr x) := by
  have := holds_plin (f := permCT P) hp (fun i _ => by rw [permCT_nat hA]; exact permCN_lt _ _) hX
  rwa [combN_congr x (m' := fun i => permCN arr (2 ^ i)) (fun i _ => permCT_nat hA _),
    ← permCN_lin] at this

theorem holds_permD {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) {S X p x : ℕ} (hp : p < S)
    (hX : Holds 12 S X p x) : Holds 12 S (plin S (basisImg (permDT P)) X) p (permDN arr x) := by
  have := holds_plin (f := permDT P) hp (fun i _ => by rw [permDT_nat hA]; exact permDN_lt _ _) hX
  rwa [combN_congr x (m' := fun i => permDN arr (2 ^ i)) (fun i _ => permDT_nat hA _),
    ← permDN_lin] at this

@[expose] noncomputable def imgP (arr : Array ℕ) (a d : ℕ) : ℕ × ℕ :=
  (permCN arr a, thetaN (permCN arr a) ^^^ permDN arr (thetaN a ^^^ d))

theorem permDN_zero' (arr : Array ℕ) : permDN arr 0 = 0 := by
  have := kn_permDN_xor arr 0 0
  simp only [Nat.xor_self] at this
  exact this

theorem imgP_lt (arr : Array ℕ) (a d : ℕ) : (imgP arr a d).1 < 4096 ∧ (imgP arr a d).2 < 4096 :=
  ⟨permCN_lt _ _, Nat.xor_lt_two_pow (n := 12) (thetaN_lt _) (permDN_lt _ _)⟩

theorem imgP_zero (arr : Array ℕ) : imgP arr 0 0 = (0, 0) := by
  unfold imgP
  rw [kn_permCN_zero, thetaN_zero, Nat.xor_zero, permDN_zero', Nat.xor_zero]

theorem monoPermXOK_eq (F : Fix) (P : ℕ) (E : MonoE) : monoPermXOK F P E =
    andB (Nat.beq (monoMoveX 24 E (Nat.lor (plin SX (basisImg (permCT P)) F.keyA)
        (Nat.shiftLeft (Nat.xor (thetaPl SX (plin SX (basisImg (permCT P)) F.keyA))
          (plin SX (basisImg (permDT P)) (Nat.xor (thetaPl SX F.keyA) F.keyD))) (Nat.mul 12 SX))))
      (Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul 12 SX))))
    (Nat.beq E.sgX (quadPl SX (betaTabT P) F.keyA)) := rfl

theorem perm_hL {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) (F : Fix) :
    ∀ p < SX, ∀ b < 24, (Nat.lor (plin SX (basisImg (permCT P)) F.keyA)
        (Nat.shiftLeft (Nat.xor (thetaPl SX (plin SX (basisImg (permCT P)) F.keyA))
          (plin SX (basisImg (permDT P)) (Nat.xor (thetaPl SX F.keyA) F.keyD))) (Nat.mul 12 SX))).testBit
        (b * SX + p) =
      if b < 12 then (imgP arr (pv SX F.keyA p) (pv SX F.keyD p)).1.testBit b
      else (imgP arr (pv SX F.keyA p) (pv SX F.keyD p)).2.testBit (b - 12) := by
  intro p hp b hb
  rw [testBit_split12 (plin_lt _ _ _) hp]
  have hap := holds_permC hA hp (holds_pv SX F.keyA p)
  split_ifs with h
  · exact hap b h
  · exact holds_xor (holds_thetaPl hp hap) (holds_permD hA hp (holds_xor (holds_thetaPl hp
      (holds_pv SX F.keyA p)) (holds_pv SX F.keyD p))) (b - 12) (by omega)

theorem quad_kappa {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) {S X p x : ℕ} (hp : p < S)
    (hX : Holds 12 S X p x) : (quadPl S (betaTabT P) X).testBit p = kappaN arr x := by
  rw [testBit_quadPl hp hX]
  unfold kappaN
  exact xorSum_congr fun i hi => xorSum_congr fun j hj => by
    rw [Trace6091.testBit_betaTabT hA.pe hi hj, ← CFSG.Monster.B.Rep4371.native_betaPN]

theorem xT_perm (hG : KeysGood) {arr : Array ℕ} (hv : Native.permValid arr = true) {p : ℕ}
    (hp : p < 98280) :
    Native.GD.xT (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) p =
      [((Native.mkCtx ()).find (imgP arr (keyQ p).1 (keyQ p).2).1 (imgP arr (keyQ p).1 (keyQ p).2).2,
        sgnI (kappaN arr (keyQ p).1))] := by
  have hb := hG.1 p hp
  unfold Native.GD.xT
  simp only [Native.GD.ofGen]
  rw [mkCtx_keys hp, mkCtx_th, fastAct_perm hv hb.1 hb.2]
  rfl

theorem perm_parts {F : Fix} {arr : Array ℕ} (hsz : arr.size = 24) {E : MonoE}
    (hE : monoEntOK F (arrList arr) E = true) :
    monoNetsOK E = true ∧ monoPadOK E = true ∧ Native.permValid arr = true ∧
      ArrOK arr (listPack (arrList arr)).1 ∧ monoPermXOK F (listPack (arrList arr)).1 E = true ∧
      monoPermWOK (listPack (arrList arr)).1 E = true ∧
      monoPermAOK (listPack (arrList arr)).1 E = true := by
  unfold monoEntOK at hE
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hE
  obtain ⟨⟨hNets, hPad⟩, hE2⟩ := hE
  have hlen : (arrList arr).length = 24 := by rw [arrList_eq, Array.length_toList, hsz]
  have hPOK : monoPermOK F (arrList arr) E = true := by
    revert hE2 hlen
    generalize arrList arr = l
    intro hE2 hlen
    match l, hE2, hlen with
    | _ :: _ :: _, hE2, _ => exact hE2
  unfold monoPermOK at hPOK
  rw [andB_eq, Bool.and_eq_true] at hPOK
  obtain ⟨hV, hR⟩ := hPOK
  obtain ⟨hA, hv⟩ := permValidT_sound hsz hV
  generalize listPack (arrList arr) = LP at hR hA ⊢
  obtain ⟨P, rest⟩ := LP
  change andB (monoPermXOK F P E) (andB (monoPermWOK P E) (monoPermAOK P E)) = true at hR
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hR
  exact ⟨hNets, hPad, hv, hA, hR.1, hR.2.1, hR.2.2⟩

theorem testBit_63 (k : ℕ) : (63 : ℕ).testBit k = decide (k < 6) := by
  rw [show (63 : ℕ) = 2 ^ 6 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem testBit_pi0N (x k : ℕ) :
    (pi0N x).testBit k = (x.testBit k ^^ (decide (k < 6) && x.testBit 0)) := by
  unfold pi0N
  rw [Nat.testBit_xor]
  cases h : x.testBit 0
  · simp
  · simp [testBit_63]

theorem pi0N_pi0N (x : ℕ) : pi0N (pi0N x) = pi0N x :=
  Nat.eq_of_testBit_eq fun k => by
    rw [testBit_pi0N, testBit_pi0N x 0]
    simp

theorem rowC_even (r : ℕ) : (Native.rowC r).testBit 0 = false := by
  unfold Native.rowC
  rw [Nat.testBit_zero]
  simp

theorem pi0N_rowC (r : ℕ) : pi0N (Native.rowC r) = Native.rowC r := by
  unfold pi0N
  rw [rowC_even]
  simp

theorem testBit_rowIdx (η : Bool) (c m : ℕ) :
    (Native.rowIdx η c).testBit m =
      if m < 11 then (pi0N c).testBit (m + 1) else (decide (m = 11) && η) := by
  have e : Native.rowIdx η c = 2 ^ 11 * η.toNat + pi0N c / 2 % 2048 := by
    unfold Native.rowIdx
    cases η <;> simp
  rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by decide))]
  split_ifs with hm
  · rw [Nat.testBit_mod_two_pow, decide_eq_true hm, Bool.true_and,
      show (2 : ℕ) = 2 ^ 1 from rfl, Nat.testBit_div_two_pow]
  · rw [Trace6091.testBit_toNat]
    by_cases h11 : m = 11
    · subst h11
      simp
    · rw [decide_eq_false (by omega : ¬ m - 11 = 0), decide_eq_false h11]
      simp

theorem rowIdx_lt (η : Bool) (c : ℕ) : Native.rowIdx η c < 4096 := by
  unfold Native.rowIdx
  have := Nat.mod_lt (pi0N c / 2) (show 2048 > 0 by decide)
  cases η <;> simp <;> omega

theorem testBit_rowC (r b : ℕ) :
    (Native.rowC r).testBit b = (decide (1 ≤ b) && decide (b - 1 < 11) && r.testBit (b - 1)) := by
  unfold Native.rowC
  have e : 2 * (r % 2048) = (r % 2048) <<< 1 := by rw [Nat.shiftLeft_eq]; ring
  rw [e, Nat.testBit_shiftLeft, show (2048 : ℕ) = 2 ^ 11 from rfl, Nat.testBit_mod_two_pow]
  simp only [ge_iff_le, Bool.and_assoc]

theorem idPlaneSX_lt {b : ℕ} (hb : b < 17) : idPlane SX b < 2 ^ SX :=
  lt_of_bits fun i hi => by
    rw [idPlane_SX hb, Bool.and_eq_true, decide_eq_true_iff] at hi
    exact hi.1

theorem holds_rowCode {p : ℕ} (hp : p < SX) : Holds 12 SX rowCodeP p (Native.rowC (p / 32)) := by
  intro b hb
  unfold rowCodeP
  refine (testBit_orLoop' (fun k => Nat.shiftLeft (idPlane SX (Nat.add k 5)) (Nat.mul (Nat.add k 1) SX))
    _ 11).trans ?_
  rw [testBit_rowC]
  have hr : ∀ k < 11, (Nat.shiftLeft (idPlane SX (Nat.add k 5)) (Nat.mul (Nat.add k 1) SX)).testBit
      (b * SX + p) = (decide (k + 1 = b) && p.testBit (k + 5)) := by
    intro k hk
    have := testBit_shl_plane (S := SX) (x := idPlane SX (k + 5)) (c := k + 1) (b := b)
      (idPlaneSX_lt (by omega)) hp
    refine this.trans ?_
    rw [idPlane_SX (by omega), decide_eq_true hp, Bool.true_and]
  have hpb : (p / 32).testBit (b - 1) = p.testBit (b - 1 + 5) := by
    rw [show (32 : ℕ) = 2 ^ 5 from rfl, Nat.testBit_div_two_pow]
  rw [hpb]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨k, hk, e⟩
    rw [hr k hk, Bool.and_eq_true, decide_eq_true_iff] at e
    obtain ⟨rfl, e⟩ := e
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rwa [Nat.add_sub_cancel]
  · simp only [Bool.and_eq_true, decide_eq_true_iff]
    rintro ⟨⟨h1, h2⟩, e⟩
    refine ⟨b - 1, h2, ?_⟩
    rw [hr _ h2, decide_eq_true (by omega), Bool.true_and]
    exact e

@[expose] noncomputable def rowNewOf (rm : Bool → ℕ → Bool × Bool × ℕ) (r : ℕ) : ℕ :=
  Native.rowIdx (rm (Native.rowEta r) (Native.rowC r)).2.1 (rm (Native.rowEta r) (Native.rowC r)).2.2

theorem rowEta_bit {p : ℕ} (hp : p < SX) : p.testBit 16 = Native.rowEta (p / 32) := by
  unfold Native.rowEta
  rw [show p.testBit 16 = (p / 32).testBit 11 by
    rw [show (32 : ℕ) = 2 ^ 5 from rfl, Nat.testBit_div_two_pow]]
  exact Benes.testBit_top (b := 11) (by
    have : SX = 131072 := rfl
    rw [show (2 : ℕ) ^ (11 + 1) = 4096 by norm_num]
    omega)

theorem permG_get {arr : Array ℕ} {j c : ℕ} (hj : j < 24) (hc : c < 24) :
    (Native.permG arr)[j * 24 + c]! = if arr[j]! = c then sgnI false else 0 := by
  unfold Native.permG
  rw [getElem!_pos (Array.ofFn _) (j * 24 + c) (by simp; omega), Array.getElem_ofFn]
  have e1 : (j * 24 + c) / 24 = j := by omega
  have e2 : (j * 24 + c) % 24 = c := by omega
  simp only [e1, e2]
  rfl

theorem monoG_perm {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) :
    MonoG (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) (fun j => arr[j]!) (fun _ => false) where
  lt := hA.lt
  inj := hA.inj
  get j hj c hc := by
    have hGG : (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).G = Native.permG arr := by
      simp only [Native.GD.ofGen]
    rw [hGG]
    exact permG_get hj hc

@[expose] noncomputable def pcP (P : ℕ) : ℕ := plin SX (basisImg (permCT P)) rowCodeP

@[expose] noncomputable def lowPP (P : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.lor acc (Nat.shiftLeft
    (Bool.rec (motive := fun _ => ℕ) (plane SX k (pcP P)) (Nat.xor (plane SX k (pcP P)) (plane SX 0 (pcP P)))
      (andB (Nat.blt 0 k) (Nat.blt k 6))) (Nat.mul k SX))) 12

@[expose] noncomputable def etaP (P : ℕ) : ℕ := Nat.xor (idPlane SX 16) (selB (kappaT (betaTabT P) 63) (ones SX))

@[expose] noncomputable def selWP (P b : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (etaP P) (plane SX (Nat.sub b 4) (lowPP P)) (Nat.blt b 16))
    (plane SX b (lookP SX 0 P)) (Nat.blt b 5)

@[expose] noncomputable def LWP (P : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc
    (Nat.shiftLeft (mux SX valW (selWP P b) (idPlane SX b)) (Nat.mul b SX))) 17

@[expose] noncomputable def sgWP (P : ℕ) : ℕ :=
  Nat.xor (quadPl SX (betaTabT P) rowCodeP) (Nat.land (etaP P) (plane SX 0 (pcP P)))

theorem monoPermWOK_eq (P : ℕ) (E : MonoE) : monoPermWOK P E =
    andB (eqOn SX 17 valW (monoW 17 E (LWP P)) (idP 17)) (Nat.beq E.sgW (Nat.land valW (sgWP P))) :=
  rfl

theorem ePermT_0 (arr : Array ℕ) (η : Bool) (c : ℕ) :
    (Native.ePermT arr (Native.betaTab arr) η c).1 =
      (Native.kappaT (Native.betaTab arr) (pi0N c) ^^
        ((η ^^ Native.kappaT (Native.betaTab arr) 63) && (permCN arr (pi0N c)).testBit 0)) := by
  simp only [Native.ePermT, mu0N]

theorem ePermT_1 (arr : Array ℕ) (η : Bool) (c : ℕ) :
    (Native.ePermT arr (Native.betaTab arr) η c).2.1 = (η ^^ Native.kappaT (Native.betaTab arr) 63) := by
  simp only [Native.ePermT]

theorem ePermT_2 (arr : Array ℕ) (η : Bool) (c : ℕ) :
    (Native.ePermT arr (Native.betaTab arr) η c).2.2 = pi0N (permCN arr (pi0N c)) := by
  simp only [Native.ePermT]

theorem testBit_32mul (R : ℕ) {a : ℕ} (ha : a < 32) (b : ℕ) :
    (32 * R + a).testBit b = if b < 5 then a.testBit b else R.testBit (b - 5) :=
  Nat.testBit_two_pow_mul_add R (i := 5) (by simpa using ha) b

theorem rowNewOf_eq (rm : Bool → ℕ → Bool × Bool × ℕ) (r : ℕ) : rowNewOf rm r =
    Native.rowIdx (rm (Native.rowEta r) (Native.rowC r)).2.1 (rm (Native.rowEta r) (Native.rowC r)).2.2 :=
  rfl

theorem kappa63 {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) :
    kappaT (betaTabT P) 63 = (kappaN arr 63).toNat := by
  rw [Trace6091.kappaT_eq hA.pe, ← CFSG.Monster.B.Rep4371.native_kappaN]

theorem holds_pcP {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) {p : ℕ} (hp : p < SX) :
    Holds 12 SX (pcP P) p (permCN arr (Native.rowC (p / 32))) :=
  holds_permC hA hp (holds_rowCode hp)

theorem etaP_bit {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) {p : ℕ} (hp : p < SX) :
    (etaP P).testBit p = (Native.rowEta (p / 32) ^^ kappaN arr 63) := by
  unfold etaP
  rw [nxor, Nat.testBit_xor, idPlane_SX (by norm_num), decide_eq_true hp, Bool.true_and, kappa63 hA,
    testBit_selB_toNat, testBit_ones, decide_eq_true hp, Bool.and_true, rowEta_bit hp]

theorem lowP_bit {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) {p k : ℕ} (hp : p < SX) (hk1 : 1 ≤ k)
    (hk : k < 12) :
    (lowPP P).testBit (k * SX + p) = (pi0N (permCN arr (Native.rowC (p / 32)))).testBit k := by
  have hpc := holds_pcP hA hp
  unfold lowPP
  refine (testBit_planeLoop (n := 12) (fun k => Bool.rec (motive := fun _ => ℕ) (plane SX k (pcP P))
      (Nat.xor (plane SX k (pcP P)) (plane SX 0 (pcP P))) (andB (Nat.blt 0 k) (Nat.blt k 6)))
    (fun k => Nat.mul k SX) (fun _ => rfl) (fun k _ => ?_) hk hp).trans ?_
  · cases andB (Nat.blt 0 k) (Nat.blt k 6)
    · exact plane_lt' _ _ _
    · exact Nat.xor_lt_two_pow (plane_lt' _ _ _) (plane_lt' _ _ _)
  · rw [testBit_pi0N]
    by_cases h6 : k < 6
    · rw [ListAux.blt_t (by omega : 0 < k), ListAux.blt_t h6]
      change (Nat.xor (plane SX k (pcP P)) (plane SX 0 (pcP P))).testBit p = _
      rw [nxor, Nat.testBit_xor, testBit_plane' hp, testBit_plane' hp, hpc k hk, hpc 0 (by norm_num),
        decide_eq_true h6, Bool.true_and]
    · rw [ListAux.blt_t (by omega : 0 < k), ListAux.blt_f (by omega : 6 ≤ k)]
      change (plane SX k (pcP P)).testBit p = _
      rw [testBit_plane' hp, hpc k hk, decide_eq_false h6, Bool.false_and, Bool.xor_false]

theorem perm_labW {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) :
    ∀ p < SX, p % 32 < 24 → Holds 17 SX (LWP P) p
      (32 * rowNewOf (Native.ePermT arr (Native.betaTab arr)) (p / 32) + arr[p % 32]!) := by
  intro p hp hm b hb
  have hc := hA.lt _ hm
  have hpw : valW.testBit p = true := by rw [testBit_valW, decide_eq_true ⟨hp, hm⟩]
  unfold LWP
  refine (testBit_muxLoop valW_lt _ _ hb hp).trans ?_
  rw [hpw, if_pos rfl, testBit_32mul _ (by omega)]
  unfold selWP
  by_cases h5 : b < 5
  · rw [ListAux.blt_t h5, if_pos h5]
    change (plane SX b (lookP SX 0 P)).testBit p = _
    rw [testBit_plane' hp]
    refine (testBit_lookP (K := 17) (o := 0) (P := P) (p := p) (b := b) (by norm_num) hp h5).trans ?_
    rw [Nat.shiftRight_zero, decide_eq_true hm, Bool.true_and, hA.pe _ hm]
  · rw [ListAux.blt_f (by omega : 5 ≤ b), if_neg h5, rowNewOf_eq, testBit_rowIdx, ePermT_2, ePermT_1,
      pi0N_rowC, pi0N_pi0N, kn_kappaT_eq]
    by_cases h16 : b < 16
    · rw [ListAux.blt_t h16, if_pos (by omega : b - 5 < 11)]
      change (plane SX (b - 4) (lowPP P)).testBit p = _
      rw [testBit_plane' hp, lowP_bit hA hp (by omega) (by omega), show b - 5 + 1 = b - 4 by omega]
    · rw [ListAux.blt_f (by omega : 16 ≤ b), if_neg (by omega : ¬ b - 5 < 11),
        decide_eq_true (by omega : b - 5 = 11), Bool.true_and]
      exact etaP_bit hA hp

theorem perm_sgW {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) {p : ℕ} (hp : p < SX) :
    (sgWP P).testBit p =
      (Native.ePermT arr (Native.betaTab arr) (Native.rowEta (p / 32)) (Native.rowC (p / 32))).1 := by
  unfold sgWP
  rw [nxor, Nat.testBit_xor, quad_kappa hA hp (holds_rowCode hp), nland, Nat.testBit_and,
    etaP_bit hA hp, testBit_plane' hp, holds_pcP hA hp 0 (by norm_num), ePermT_0, pi0N_rowC,
    kn_kappaT_eq, kn_kappaT_eq]

theorem perm_W {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {arr : Array ℕ} {P : ℕ}
    (hA : ArrOK arr P) {E : MonoE} (hNets : monoNetsOK E = true) (hW : monoPermWOK P E = true)
    {v : Native.DVec} {W : ℕ}
    (hW1 : ∀ r < 4096, ∀ j < 24, resPN n SX W (32 * r + j) = resN n v (98580 + 24 * r + j))
    (hW2 : ∀ p < SX, 24 ≤ p % 32 → resPN n SX W p = 0) (hW3 : W < 2 ^ (n * SX)) :
    (∀ r < 4096, ∀ j < 24, resPN n SX (monoW n E (negMN SX n E.sgW W)) (32 * r + j) =
      resN n (Native.applyGen (Native.mkCtx ()) (.perm arr) v) (98580 + 24 * r + j)) ∧
    (∀ p < SX, 24 ≤ p % 32 → resPN n SX (monoW n E (negMN SX n E.sgW W)) p = 0) ∧
      monoW n E (negMN SX n E.sgW W) < 2 ^ (n * SX) := by
  obtain ⟨π, hP⟩ := pg_monoW hNets
  have hSX : SX = 131072 := rfl
  have hrlt : ∀ r < 4096, rowNewOf (Native.ePermT arr (Native.betaTab arr)) r < 4096 :=
    fun r _ => rowIdx_lt _ _
  have hlab := perm_labW hA
  rw [monoPermWOK_eq, andB_eq, Bool.and_eq_true, Nat.beq_eq] at hW
  obtain ⟨hchk, hsgc⟩ := hW
  have hvb : ∀ p, valW.testBit p = true ↔ p < SX ∧ p % 32 < 24 := fun p => by
    rw [testBit_valW, decide_eq_true_iff]
  obtain ⟨part1, part2⟩ := labels_pi (k := 17) SX_eq hP valW_lt
    (fun p => 32 * rowNewOf (Native.ePermT arr (Native.betaTab arr)) (p / 32) + arr[p % 32]!) hchk
    (fun p hp hm => hlab p hp ((hvb p).1 hm).2)
    (fun p hp hm b hb => by
      refine (testBit_muxLoop valW_lt _ _ hb hp).trans ?_
      rw [hm, if_neg (by decide), idPlane_SX hb, decide_eq_true hp, Bool.true_and])
    (fun p hp hm => by
      have hm' := ((hvb p).1 hm).2
      have h1 := hrlt (p / 32) (by omega)
      have h2 := hA.lt _ hm'
      refine ⟨by omega, (hvb _).2 ⟨by omega, by omega⟩⟩)
  have hsrc : ∀ x, x < SX → x % 32 < 24 → π x < SX ∧ π x % 32 < 24 ∧
      32 * rowNewOf (Native.ePermT arr (Native.betaTab arr)) (π x / 32) + arr[π x % 32]! = x := by
    intro x hx hm
    obtain ⟨h1, h2⟩ := part1 x hx ((hvb x).2 ⟨hx, hm⟩)
    exact ⟨hP.g.lt x hx, ((hvb _).1 h1).2, h2⟩
  have hrsurj : ∀ r' < 4096, ∃ r < 4096, rowNewOf (Native.ePermT arr (Native.betaTab arr)) r = r' := by
    intro r' hr'
    obtain ⟨h1, h2, h3⟩ := hsrc (32 * r') (by omega) (by omega)
    have := hA.lt _ h2
    exact ⟨π (32 * r') / 32, by omega, by omega⟩
  have hrinj := inj_of_surj hrlt hrsurj
  have hπ : ∀ r < 4096, ∀ c < 24,
      π (32 * rowNewOf (Native.ePermT arr (Native.betaTab arr)) r + arr[c]!) = 32 * r + c := by
    intro r hr c hc
    have h0 := hrlt r hr
    have h0' := hA.lt c hc
    obtain ⟨h1, h2, h3⟩ := hsrc (32 * rowNewOf (Native.ePermT arr (Native.betaTab arr)) r + arr[c]!)
      (by omega) (by omega)
    have h4 := hA.lt _ h2
    have e1 : arr[π (32 * rowNewOf (Native.ePermT arr (Native.betaTab arr)) r + arr[c]!) % 32]! =
        arr[c]! := by omega
    have e2 := hA.inj _ h2 _ hc e1
    have e3 := hrinj _ (by omega) _ hr (by omega : rowNewOf (Native.ePermT arr (Native.betaTab arr))
      (π (32 * rowNewOf (Native.ePermT arr (Native.betaTab arr)) r + arr[c]!) / 32) =
        rowNewOf (Native.ePermT arr (Native.betaTab arr)) r)
    omega
  have hpad : ∀ x < SX, 24 ≤ x % 32 → 24 ≤ π x % 32 := by
    intro x hx hm
    have := part2 (fun p hp p' hp' hm1 hm2 e => by
      have a1 := ((hvb p).1 hm1).2
      have a2 := ((hvb p').1 hm2).2
      have b1 := hA.lt _ a1
      have b2 := hA.lt _ a2
      have c1 := hrlt (p / 32) (by omega)
      have c2 := hrlt (p' / 32) (by omega)
      have e1 := hA.inj _ a1 _ a2 (by omega)
      have e2 := hrinj _ (by omega) _ (by omega) (by omega : rowNewOf (Native.ePermT arr
        (Native.betaTab arr)) (p / 32) = rowNewOf (Native.ePermT arr (Native.betaTab arr)) (p' / 32))
      omega) x hx (by
        cases h : valW.testBit x
        · rfl
        · exact absurd ((hvb x).1 h).2 (by omega))
    by_contra hc
    exact absurd ((hvb _).2 ⟨hP.g.lt x hx, by omega⟩) (by rw [this]; decide)
  have hsg : ∀ r < 4096, ∀ c < 24, E.sgW.testBit (32 * r + c) =
      ((Native.ePermT arr (Native.betaTab arr) (Native.rowEta r) (Native.rowC r)).1 ^^ false) := by
    intro r hr c hc
    rw [hsgc, nland, Nat.testBit_and, (hvb _).2 ⟨by omega, by omega⟩, Bool.true_and, Bool.xor_false,
      perm_sgW hA (by omega), show (32 * r + c) / 32 = r by omega]
  have hgW : (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).rowT =
      Native.monoRows (Native.ePermT arr (Native.betaTab arr)) := by
    simp only [Native.GD.ofGen]
  have hl0 : (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).latS = 0 := by simp only [Native.GD.ofGen]
  have hr0 : (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).rowS = 0 := by simp only [Native.GD.ofGen]
  exact moveW_sound hn hlg hNets hP hl0 hr0 hgW (monoG_perm hA) (fun r _ => rfl) hrlt hrinj hπ hpad
    hsg hW1 hW2 hW3

@[expose] noncomputable def selAP (P b : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (plane SA (Nat.sub b 5) (lookP SA 5 P)) (plane SA b (lookP SA 0 P))
    (Nat.blt b 5)

@[expose] noncomputable def LAP (P : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc
    (Nat.shiftLeft (mux SA valA (selAP P b) (idPlane SA b)) (Nat.mul b SA))) 10

theorem monoPermAOK_eq (P : ℕ) (E : MonoE) : monoPermAOK P E =
    andB (Nat.beq E.sgA 0) (eqOn SA 10 valA (amapN 10 E.cn (LAP P)) (idP 10)) := rfl

theorem perm_labA {arr : Array ℕ} {P : ℕ} (hA : ArrOK arr P) :
    ∀ p < SA, p % 32 < 24 → p / 32 < 24 → Holds 10 SA (LAP P) p (32 * arr[p / 32]! + arr[p % 32]!) := by
  intro p hp hm hd b hb
  have hc := hA.lt _ hm
  have hpw : valA.testBit p = true := by rw [testBit_valA, decide_eq_true ⟨hp, hm, hd⟩]
  unfold LAP
  refine (testBit_muxLoop valA_lt _ _ hb hp).trans ?_
  rw [hpw, if_pos rfl, testBit_32mul _ (by omega)]
  unfold selAP
  by_cases h5 : b < 5
  · rw [ListAux.blt_t h5, if_pos h5]
    change (plane SA b (lookP SA 0 P)).testBit p = _
    rw [testBit_plane' hp]
    refine (testBit_lookP (K := 10) (o := 0) (P := P) (p := p) (b := b) (by norm_num) hp h5).trans ?_
    rw [Nat.shiftRight_zero, decide_eq_true hm, Bool.true_and, hA.pe _ hm]
  · rw [ListAux.blt_f (by omega : 5 ≤ b), if_neg h5]
    change (plane SA (b - 5) (lookP SA 5 P)).testBit p = _
    rw [testBit_plane' hp]
    have hs : (p >>> 5) % 32 = p / 32 := by
      rw [Nat.shiftRight_eq_div_pow]
      have : SA = 1024 := rfl
      exact Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)
    refine (testBit_lookP (K := 10) (o := 5) (P := P) (p := p) (b := b - 5) (by norm_num) hp
      (by omega)).trans ?_
    rw [hs, decide_eq_true hd, Bool.true_and, hA.pe _ hd]

theorem perm_A {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {arr : Array ℕ} {P : ℕ}
    (hA : ArrOK arr P) {E : MonoE} (hNets : monoNetsOK E = true) (hAA : monoPermAOK P E = true)
    {v : Native.DVec} {A : ℕ}
    (hA1 : ∀ i < 24, ∀ j < 24, resPN n SA A (32 * i + j) = resN n v (Native.aIdx i j))
    (hA2 : ∀ p < SA, (24 ≤ p % 32 ∨ 24 ≤ p / 32) → resPN n SA A p = 0) (hA3 : A < 2 ^ (n * SA)) :
    (∀ i < 24, ∀ j < 24, resPN n SA (amapN n E.cn (negMN SA n E.sgA A)) (32 * i + j) =
      resN n (Native.applyGen (Native.mkCtx ()) (.perm arr) v) (Native.aIdx i j)) ∧
    (∀ p < SA, (24 ≤ p % 32 ∨ 24 ≤ p / 32) → resPN n SA (amapN n E.cn (negMN SA n E.sgA A)) p = 0) ∧
      amapN n E.cn (negMN SA n E.sgA A) < 2 ^ (n * SA) := by
  obtain ⟨π, hP⟩ := pg_amapN hNets
  have hSA : SA = 1024 := rfl
  rw [monoPermAOK_eq, andB_eq, Bool.and_eq_true, Nat.beq_eq] at hAA
  obtain ⟨hs0, hchk⟩ := hAA
  have hvb : ∀ p, valA.testBit p = true ↔ p < SA ∧ p % 32 < 24 ∧ p / 32 < 24 := fun p => by
    rw [testBit_valA, decide_eq_true_iff]
  obtain ⟨part1, part2⟩ := labels_pi (k := 10) SA_eq hP valA_lt
    (fun p => 32 * arr[p / 32]! + arr[p % 32]!) hchk
    (fun p hp hm => perm_labA hA p hp ((hvb p).1 hm).2.1 ((hvb p).1 hm).2.2)
    (fun p hp hm b hb => by
      refine (testBit_muxLoop valA_lt _ _ hb hp).trans ?_
      rw [hm, if_neg (by decide), idPlane_SA hb, decide_eq_true hp, Bool.true_and])
    (fun p hp hm => by
      obtain ⟨-, h1, h2⟩ := (hvb p).1 hm
      have a1 := hA.lt _ h1
      have a2 := hA.lt _ h2
      exact ⟨by omega, (hvb _).2 ⟨by omega, by omega, by omega⟩⟩)
  have hπ : ∀ i < 24, ∀ j < 24, π (32 * arr[i]! + arr[j]!) = 32 * i + j := by
    intro i hi j hj
    have a1 := hA.lt _ hi
    have a2 := hA.lt _ hj
    obtain ⟨h1, h2⟩ := part1 (32 * arr[i]! + arr[j]!) (by omega) ((hvb _).2 ⟨by omega, by omega, by omega⟩)
    obtain ⟨-, h3, h4⟩ := (hvb _).1 h1
    beta_reduce at h2
    have b1 := hA.lt _ h3
    have b2 := hA.lt _ h4
    have e1 := hA.inj _ h3 _ hj (by omega)
    have e2 := hA.inj _ h4 _ hi (by omega)
    omega
  have hpad : ∀ x < SA, (24 ≤ x % 32 ∨ 24 ≤ x / 32) → (24 ≤ π x % 32 ∨ 24 ≤ π x / 32) := by
    intro x hx hm
    have := part2 (fun p hp p' hp' hm1 hm2 e => by
      obtain ⟨-, a1, a2⟩ := (hvb p).1 hm1
      obtain ⟨-, a3, a4⟩ := (hvb p').1 hm2
      beta_reduce at e
      have b1 := hA.lt _ a1
      have b2 := hA.lt _ a2
      have b3 := hA.lt _ a3
      have b4 := hA.lt _ a4
      have e1 := hA.inj _ a1 _ a3 (by omega)
      have e2 := hA.inj _ a2 _ a4 (by omega)
      omega) x hx (by
        cases h : valA.testBit x
        · rfl
        · obtain ⟨-, h1, h2⟩ := (hvb x).1 h
          omega)
    by_contra hc
    have hpx := hP.g.lt x hx
    exact absurd ((hvb _).2 ⟨hpx, by omega, by omega⟩) (by rw [this]; decide)
  have hsg : ∀ i < 24, ∀ j < 24, E.sgA.testBit (32 * i + j) = ((fun _ => false) i ^^ (fun _ => false) j) := by
    intro i _ j _
    rw [hs0, Nat.zero_testBit]
    rfl
  have hl0 : (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)).latS = 0 := by simp only [Native.GD.ofGen]
  exact moveA_sound hn hlg hNets hP hl0 (monoG_perm hA) hπ hpad hsg hA1 hA2 hA3

theorem holds_congr {n S X p x y : ℕ} (h : Holds n S X p x) (e : x = y) : Holds n S X p y := e ▸ h

theorem testBit_xorSel' {S K m p : ℕ} (hp : p < S) :
    (xorSel S K m).testBit p = xorSum (fun i => m.testBit i && K.testBit (i * S + p)) 12 := by
  refine (testBit_xorLoop (fun i => selB (bitN m i) (plane S i K)) p 12).trans ?_
  exact xorSum_congr fun i _ => by rw [testBit_selB_bitN, testBit_plane' hp]

theorem pairN_xs (a d : ℕ) : pairN a d = xorSum (fun i => a.testBit i && d.testBit i) 12 := by
  unfold pairN
  rw [parN_xorSum]
  exact xorSum_congr fun i _ => Nat.testBit_and a d i

theorem pairN_comm' (a d : ℕ) : pairN a d = pairN d a := by
  unfold pairN
  rw [Nat.and_comm]

theorem pairN_zero_r' (a : ℕ) : pairN a 0 = false := kn_pairN_zero_r a

theorem pairN_zero_l' (a : ℕ) : pairN 0 a = false := kn_pairN_zero_l a

theorem parSel_holds {S K p x : ℕ} (hp : p < S) (hK : Holds 12 S K p x) (m : ℕ) :
    (parSel S m K).testBit p = pairN m x := by
  unfold parSel
  rw [testBit_xorSel' hp, pairN_xs]
  exact xorSum_congr fun i hi => by rw [hK i hi]

theorem parSel_lt (S m K : ℕ) : parSel S m K < 2 ^ S :=
  xorLoop_lt (fun i => selB (bitN m i) (plane S i K))
    (fun i => by rw [bitN_eq_toNat]; exact selB_toNat_lt (plane_lt' S i K)) 12

theorem repP_lt {S m : ℕ} (hm : m < 2 ^ S) (n : ℕ) : repP S n m < 2 ^ (n * S) :=
  planeLoop_lt (fun _ => m) (fun k => Nat.mul k S) (fun _ => rfl) (fun _ _ => hm)

theorem holds_repP6 {S m p : ℕ} (hm : m < 2 ^ S) (hp : p < S) :
    Holds 12 S (repP S 6 m) p (if m.testBit p then 63 else 0) := fun k hk => by
  by_cases h6 : k < 6
  · rw [testBit_repP hm h6 hp]
    cases m.testBit p <;> simp [testBit_63, h6]
  · have : 6 * S ≤ k * S := Nat.mul_le_mul_right _ (by omega)
    rw [bit_hi (repP_lt hm 6) (by omega)]
    cases m.testBit p <;> simp [testBit_63, h6]

theorem holds_constP {S c m p : ℕ} (hm : m < 2 ^ S) (hp : p < S) :
    Holds 12 S (constP S c m) p (if m.testBit p then c else 0) := fun k hk => by
  rw [testBit_constP hm hk hp]
  cases m.testBit p <;> simp

theorem constP_lt (S c m : ℕ) (hm : m < 2 ^ S) : constP S c m < 2 ^ (12 * S) :=
  planeLoop_lt (n := 12) (fun k => selB (bitN c k) m) (fun k => Nat.mul k S) (fun _ => rfl)
    (fun k _ => by rw [bitN_eq_toNat]; exact selB_toNat_lt hm)

theorem wordN_two_pow {i : ℕ} (hi : i < 12) : wordN (2 ^ i) = bmaskN i := by
  unfold wordN
  rw [combN_two_pow, if_pos hi]

theorem acodeN_lin (a b : ℕ) : acodeN a b = combN (fun i => acodeN a (2 ^ i)) 12 b := by
  unfold acodeN
  have e1 : wordN b = combN bmaskN 12 b := rfl
  rw [e1, Nat.and_comm, combN_and, combN_map dualN_xor dualN_zero]
  refine combN_congr b fun i hi => ?_
  rw [wordN_two_pow hi, Nat.and_comm]

theorem dualT_word (a x : ℕ) : dualT (Nat.land (wordT a) (wordT x)) = acodeN a x := by
  rw [Trace6091.dualT_eq, Benes.nland, Trace6091.wordT_eq, Trace6091.wordT_eq,
    ← CFSG.Monster.B.Rep4371.native_dualN, ← CFSG.Monster.B.Rep4371.native_wordN]
  rfl

theorem holds_acode {S X p b : ℕ} (hp : p < S) (hX : Holds 12 S X p b) (a : ℕ) :
    Holds 12 S (plin S (basisImg (fun x => dualT (Nat.land (wordT a) (wordT x)))) X) p (acodeN a b) := by
  have := holds_plin (f := fun x => dualT (Nat.land (wordT a) (wordT x))) hp
    (fun i _ => by rw [dualT_word]; exact dualN_lt _) hX
  rwa [combN_congr b (m' := fun i => acodeN a (2 ^ i)) (fun i _ => dualT_word a _), ← acodeN_lin] at this

theorem thetaT_nat (a : ℕ) : thetaT a = thetaN a := by
  rw [Trace6091.thetaT_eq, ← CFSG.Monster.B.Rep4371.native_thetaN]

theorem testBit_parP {S X Y p x y : ℕ} (hp : p < S) (hX : Holds 12 S X p x) (hY : Holds 12 S Y p y) :
    (parP S X Y).testBit p = pairN x y := by
  unfold parP
  refine (testBit_xorLoop (fun k => Nat.land (plane S k X) (plane S k Y)) p 12).trans ?_
  rw [pairN_xs]
  exact xorSum_congr fun k hk => by
    rw [Benes.nland, Nat.testBit_and, testBit_plane' hp, testBit_plane' hp, hX k hk, hY k hk]

@[expose] noncomputable def daS (a d : ℕ) : ℕ :=
  (if pairN 63 d then a else 0) ^^^ (if (pairN 63 d && pN a) ^^ pairN a d then 63 else 0)

@[expose] noncomputable def imgS (a b d : ℕ) : ℕ × ℕ :=
  ((b ^^^ (if thetaBit a b then 63 else 0) ^^^ daS a d) % 4096,
    (acodeN a b ^^^ ((if pairN 63 d then thetaN a else 0) ^^^ d)) % 4096)

@[expose] noncomputable def sgS (a b d : ℕ) : Bool :=
  thetaBit b a ^^ (!pairN 63 d && pairN a d) ^^ pairN (daS a d) (acodeN a b)

@[expose] noncomputable def OS (F : Fix) : ℕ := parSel SX 63 F.keyD
@[expose] noncomputable def PadS (F : Fix) (a : ℕ) : ℕ := parSel SX a F.keyD
@[expose] noncomputable def T1S (F : Fix) (a : ℕ) : ℕ := Nat.xor F.keyA (repP SX 6 (parSel SX (thetaT a) F.keyA))
@[expose] noncomputable def Dd1S (F : Fix) (a : ℕ) : ℕ :=
  Nat.xor (constP SX a (OS F)) (repP SX 6 (Nat.xor (selB (pT a) (OS F)) (PadS F a)))
@[expose] noncomputable def T2S (F : Fix) (a : ℕ) : ℕ :=
  plin SX (basisImg (fun b => dualT (Nat.land (wordT a) (wordT b)))) F.keyA
@[expose] noncomputable def Dd2S (F : Fix) (a : ℕ) : ℕ := Nat.xor F.keyD (constP SX (thetaT a) (OS F))
@[expose] noncomputable def T0S (F : Fix) (a : ℕ) : ℕ := parSel SX a (thetaPl SX F.keyA)
@[expose] noncomputable def Dd0S (F : Fix) (a : ℕ) : ℕ := Nat.land (Nat.xor (ones SX) (OS F)) (PadS F a)

theorem monoSignXOK_eq (F : Fix) (a : ℕ) (E : MonoE) : monoSignXOK F a E =
    andB (Nat.beq (monoMoveX 24 E (Nat.lor (Nat.xor (T1S F a) (Dd1S F a))
        (Nat.shiftLeft (Nat.xor (T2S F a) (Dd2S F a)) (Nat.mul 12 SX))))
      (Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul 12 SX))))
    (Nat.beq E.sgX (Nat.land validX (Nat.xor (Nat.xor (T0S F a) (Dd0S F a))
      (parP SX (Dd1S F a) (T2S F a))))) := rfl

theorem sign_bits {F : Fix} (a : ℕ) {p : ℕ} (hp : p < SX) :
    (OS F).testBit p = pairN 63 (pv SX F.keyD p) ∧
    (PadS F a).testBit p = pairN a (pv SX F.keyD p) ∧
    Holds 12 SX (Nat.xor (T1S F a) (Dd1S F a)) p
      (pv SX F.keyA p ^^^ (if thetaBit a (pv SX F.keyA p) then 63 else 0) ^^^ daS a (pv SX F.keyD p)) ∧
    Holds 12 SX (Dd1S F a) p (daS a (pv SX F.keyD p)) ∧
    Holds 12 SX (T2S F a) p (acodeN a (pv SX F.keyA p)) ∧
    Holds 12 SX (Dd2S F a) p ((if pairN 63 (pv SX F.keyD p) then thetaN a else 0) ^^^ pv SX F.keyD p) := by
  have hA := holds_pv SX F.keyA p
  have hD := holds_pv SX F.keyD p
  have hO : (OS F).testBit p = pairN 63 (pv SX F.keyD p) := parSel_holds hp hD 63
  have hPd : (PadS F a).testBit p = pairN a (pv SX F.keyD p) := parSel_holds hp hD a
  have hOl : OS F < 2 ^ SX := parSel_lt _ _ _
  have hDd1 : Holds 12 SX (Dd1S F a) p (daS a (pv SX F.keyD p)) := by
    refine holds_congr (holds_xor (holds_constP (c := a) hOl hp)
      (holds_repP6 (Nat.xor_lt_two_pow (by rw [KeysOKAux.pT_eq]; exact selB_toNat_lt hOl)
        (parSel_lt _ _ _)) hp)) ?_
    unfold daS
    rw [hO, nxor, Nat.testBit_xor, KeysOKAux.pT_eq, testBit_selB_toNat, hO, hPd, Bool.and_comm]
  refine ⟨hO, hPd, ?_, hDd1, holds_acode hp hA a, ?_⟩
  · refine holds_congr (holds_xor (holds_xor hA (holds_repP6 (parSel_lt _ _ _) hp)) hDd1) ?_
    rw [parSel_holds hp hA, thetaT_nat]
    unfold thetaBit
    rw [pairN_comm']
  · refine holds_congr (holds_xor hD (holds_constP (c := thetaT a) hOl hp)) ?_
    rw [hO, thetaT_nat, Nat.xor_comm]

theorem imgS_lt (a b d : ℕ) : (imgS a b d).1 < 4096 ∧ (imgS a b d).2 < 4096 :=
  ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem acodeN_zero (a : ℕ) : acodeN a 0 = 0 := by
  unfold acodeN
  rw [show wordN 0 = 0 from combN_zero _ _, Nat.and_zero, dualN_zero]

theorem imgS_zero (a : ℕ) : imgS a 0 0 = (0, 0) := by
  unfold imgS daS thetaBit
  simp [pairN_zero_r', pairN_zero_l', acodeN_zero]

theorem mod4096 {x : ℕ} (h : x < 4096) : x % 4096 = x := Nat.mod_eq_of_lt h

theorem lt4096_xor {x y : ℕ} (hx : x < 4096) (hy : y < 4096) : x ^^^ y < 4096 :=
  Nat.xor_lt_two_pow (n := 12) hx hy

theorem ite63_lt (c : Prop) [Decidable c] : (if c then 63 else 0) < 4096 := by split_ifs <;> decide

theorem daS_lt {a : ℕ} (ha : a < 4096) (d : ℕ) : daS a d < 4096 := by
  unfold daS
  refine lt4096_xor ?_ (ite63_lt _)
  split_ifs
  · exact ha
  · decide

theorem conjDN_zero (a : ℕ) : conjDN a 0 = (false, 0, 0) := by
  simp [conjDN, pairN_zero_r']

theorem conjTN_zero (a : ℕ) : conjTN a 0 = (false, 0, 0) := by
  simp [conjTN, thetaBit, pairN_zero_r', pairN_zero_l', thetaN_zero, acodeN_zero]

theorem tabT_sign (a : ℕ) {b : ℕ} (hb : b < 4096) : (Native.tabT (conjYN a))[b]! = conjTN a b := by
  unfold Native.tabT
  rw [kn_map_range_get _ hb]
  simp [conjYN, Pauli.mul, Pauli.s, Pauli.a, Pauli.d, conjDN_zero, pairN_zero_r', pairN_zero_l']

theorem tabD_sign (a : ℕ) {d : ℕ} (hd : d < 4096) : (Native.tabD (conjYN a))[d]! = conjDN a d := by
  unfold Native.tabD
  rw [kn_map_range_get _ hd]
  simp [conjYN, Pauli.mul, Pauli.s, Pauli.a, Pauli.d, conjTN_zero, pairN_zero_r', pairN_zero_l']

theorem xT_sign (hG : KeysGood) {a : ℕ} (ha : a < 4096) {p : ℕ} (hp : p < 98280) :
    Native.GD.xT (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) (.sign a)) p =
      [((Native.mkCtx ()).find (imgS a (keyQ p).1 (keyQ p).2).1 (imgS a (keyQ p).1 (keyQ p).2).2,
        sgnI (sgS a (keyQ p).1 (keyQ p).2))] := by
  have hb := hG.1 p hp
  unfold Native.GD.xT
  simp only [Native.GD.ofGen]
  rw [mkCtx_keys hp]
  unfold Native.fastAct
  rw [Nat.mod_eq_of_lt hb.1, Nat.mod_eq_of_lt hb.2, tabT_sign a hb.1, tabD_sign a hb.2]
  have h1 : ((keyQ p).1 ^^^ (if thetaBit a (keyQ p).1 then 63 else 0) ^^^ daS a (keyQ p).2) % 4096 =
      (keyQ p).1 ^^^ (if thetaBit a (keyQ p).1 then 63 else 0) ^^^ daS a (keyQ p).2 :=
    mod4096 (lt4096_xor (lt4096_xor hb.1 (ite63_lt _)) (daS_lt ha _))
  have h2 : (acodeN a (keyQ p).1 ^^^ ((if pairN 63 (keyQ p).2 then thetaN a else 0) ^^^ (keyQ p).2)) % 4096 =
      acodeN a (keyQ p).1 ^^^ ((if pairN 63 (keyQ p).2 then thetaN a else 0) ^^^ (keyQ p).2) :=
    mod4096 (lt4096_xor (dualN_lt _) (lt4096_xor (by split_ifs; exact thetaN_lt _; decide) hb.2))
  simp only [imgS, sgS, h1, h2]
  simp only [Pauli.mul, Pauli.s, Pauli.a, Pauli.d, conjTN, conjDN, daS, pairN_zero_r', pairN_zero_l',
    Nat.zero_xor, Bool.false_xor, Bool.xor_false]

theorem mod2_toNat (x : ℕ) : x % 2 = (x.testBit 0).toNat := by
  rw [Nat.toNat_testBit, Nat.pow_zero, Nat.div_one]

theorem popcN_xor : ∀ k u v, popcN k (u ^^^ v) + 2 * popcN k (u &&& v) = popcN k u + popcN k v
  | 0, _, _ => rfl
  | k + 1, u, v => by
    simp only [popcN]
    have ih := popcN_xor k (u / 2) (v / 2)
    have e1 : (u ^^^ v) / 2 = u / 2 ^^^ v / 2 := by
      have := Nat.shiftRight_xor_distrib (a := u) (b := v) (i := 1)
      simpa [Nat.shiftRight_eq_div_pow] using this
    have e2 : (u &&& v) / 2 = u / 2 &&& v / 2 := by
      have := Nat.shiftRight_and_distrib (a := u) (b := v) (i := 1)
      simpa [Nat.shiftRight_eq_div_pow] using this
    have e3 : (u ^^^ v) % 2 + 2 * ((u &&& v) % 2) = u % 2 + v % 2 := by
      rw [mod2_toNat, mod2_toNat (u &&& v), mod2_toNat u, mod2_toNat v, Nat.testBit_xor, Nat.testBit_and]
      cases u.testBit 0 <;> cases v.testBit 0 <;> rfl
    rw [e1, e2]
    omega

theorem parN_def (k x : ℕ) : parN k x = decide (popcN k x % 2 = 1) := by
  unfold parN
  cases h : popcN k x % 2 == 1 <;> simp_all

theorem popc_half_xor {u v : ℕ} (hu : parN 24 u = false) (hv : parN 24 v = false) :
    parN 24 (u ^^^ v) = false ∧
      decide (popcN 24 (u ^^^ v) / 2 % 2 = 1) =
        (decide (popcN 24 u / 2 % 2 = 1) ^^ decide (popcN 24 v / 2 % 2 = 1) ^^ parN 24 (u &&& v)) := by
  have hid := popcN_xor 24 u v
  rw [parN_def] at hu hv ⊢
  rw [parN_def]
  simp only [decide_eq_false_iff_not] at hu hv
  constructor
  · simp only [decide_eq_false_iff_not]
    omega
  · rcases Nat.mod_two_eq_zero_or_one (popcN 24 u / 2) with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one (popcN 24 v / 2) with h2 | h2 <;>
      rcases Nat.mod_two_eq_zero_or_one (popcN 24 (u &&& v)) with h3 | h3 <;>
      simp only [h1, h2, h3, decide_true, decide_false] <;>
      simp <;> omega

theorem bmask_even : ∀ i < 12, ∀ j < 12, parN 24 (bmaskN j &&& bmaskN i) = false := by decide +kernel

theorem parN_and_xor (x y m : ℕ) : parN 24 ((x ^^^ y) &&& m) = (parN 24 (x &&& m) ^^ parN 24 (y &&& m)) :=
  parN_xor 24 x y m

theorem parN_combN_and (m : ℕ → ℕ) (c y : ℕ) : ∀ n,
    parN 24 (combN m n c &&& y) = xorSum (fun i => c.testBit i && parN 24 (m i &&& y)) n
  | 0 => by simp only [combN]; exact parN_zero 24 y
  | n + 1 => by
    simp only [combN, xorSum]
    rw [parN_and_xor, parN_combN_and m c y n]
    cases c.testBit n
    · simp only [Bool.false_eq_true, if_false, Bool.false_and, Bool.xor_false]
      rw [parN_zero, Bool.xor_false]
    · rfl

theorem word_even (a : ℕ) {i : ℕ} (hi : i < 12) : parN 24 (wordN a &&& bmaskN i) = false := by
  unfold wordN
  rw [parN_combN_and]
  exact (xorSum_congr fun j hj => by rw [bmask_even i hi j hj, Bool.and_false]).trans (xorSum_false 12)

theorem and3 (x y z : ℕ) : x &&& (y &&& z) = y &&& (x &&& z) :=
  Nat.eq_of_testBit_eq fun k => by
    simp only [Nat.testBit_and]
    cases x.testBit k <;> cases y.testBit k <;> rfl

theorem half_weight (a c : ℕ) : ∀ n ≤ 12,
    parN 24 (wordN a &&& combN bmaskN n c) = false ∧
      decide (popcN 24 (wordN a &&& combN bmaskN n c) / 2 % 2 = 1) =
        (xorSum (fun i => xorSum (fun j => decide (i < j) && c.testBit i && c.testBit j &&
            parN 24 (wordN a &&& (bmaskN i &&& bmaskN j))) n) n ^^
          xorSum (fun i => c.testBit i && decide (popcN 24 (wordN a &&& bmaskN i) / 2 % 2 = 1)) n)
  | 0, _ => by simp [combN, xorSum, parN_def, popcN]
  | n + 1, hn => by
    obtain ⟨ih1, ih2⟩ := half_weight a c n (by omega)
    have hstep : ∀ _j : ℕ, xorSum (fun i => xorSum (fun j => decide (i < j) && c.testBit i && c.testBit j &&
        parN 24 (wordN a &&& (bmaskN i &&& bmaskN j))) (n + 1)) (n + 1) =
        (xorSum (fun i => xorSum (fun j => decide (i < j) && c.testBit i && c.testBit j &&
          parN 24 (wordN a &&& (bmaskN i &&& bmaskN j))) n) n ^^
        xorSum (fun i => c.testBit i && c.testBit n && parN 24 (wordN a &&& (bmaskN i &&& bmaskN n))) n) := by
      intro _
      rw [xorSum]
      have hlast : xorSum (fun j => decide (n < j) && c.testBit n && c.testBit j &&
          parN 24 (wordN a &&& (bmaskN n &&& bmaskN j))) (n + 1) = false := by
        refine (xorSum_congr fun j hj => ?_).trans (xorSum_false (n + 1))
        rw [decide_eq_false (by omega)]
        simp
      rw [hlast, Bool.xor_false]
      have : (fun i => xorSum (fun j => decide (i < j) && c.testBit i && c.testBit j &&
          parN 24 (wordN a &&& (bmaskN i &&& bmaskN j))) (n + 1)) =
          fun i => (xorSum (fun j => decide (i < j) && c.testBit i && c.testBit j &&
            parN 24 (wordN a &&& (bmaskN i &&& bmaskN j))) n ^^
            (decide (i < n) && c.testBit i && c.testBit n && parN 24 (wordN a &&& (bmaskN i &&& bmaskN n)))) := by
        funext i
        rw [xorSum]
      rw [this, xorSum_xor]
      refine congrArg (Bool.xor _) ?_
      exact xorSum_congr fun i hi => by rw [decide_eq_true hi, Bool.true_and]
    rw [hstep 0]
    have ec : combN bmaskN (n + 1) c = combN bmaskN n c ^^^ (if c.testBit n then bmaskN n else 0) := rfl
    have ex : xorSum (fun i => c.testBit i && decide (popcN 24 (wordN a &&& bmaskN i) / 2 % 2 = 1))
        (n + 1) = (xorSum (fun i => c.testBit i && decide (popcN 24 (wordN a &&& bmaskN i) / 2 % 2 = 1)) n ^^
          (c.testBit n && decide (popcN 24 (wordN a &&& bmaskN n) / 2 % 2 = 1))) := rfl
    rw [ec, ex, Nat.and_xor_distrib_left]
    cases hcn : c.testBit n
    · simp only [Bool.false_eq_true, if_false, Nat.and_zero, Nat.xor_zero, Bool.false_and,
        Bool.and_false, Bool.xor_false]
      refine ⟨ih1, ?_⟩
      rw [ih2]
      simp only [xorSum_false, Bool.xor_false]
    · simp only [if_true]
      obtain ⟨h1, h2⟩ := popc_half_xor ih1 (word_even a (i := n) (by omega))
      refine ⟨h1, ?_⟩
      rw [h2, ih2]
      have hX : parN 24 ((wordN a &&& combN bmaskN n c) &&& (wordN a &&& bmaskN n)) =
          xorSum (fun i => c.testBit i && true && parN 24 (wordN a &&& (bmaskN i &&& bmaskN n))) n := by
        have e : (wordN a &&& combN bmaskN n c) &&& (wordN a &&& bmaskN n) =
            combN bmaskN n c &&& (wordN a &&& bmaskN n) := by
          rw [Nat.and_comm (wordN a), Nat.and_assoc, ← Nat.and_assoc (wordN a), Nat.and_self]
        rw [e, parN_combN_and]
        refine xorSum_congr fun i _ => ?_
        rw [Bool.and_true, and3]
      rw [hX]
      have b4 : ∀ S H D C : Bool, (((S ^^ H) ^^ D) ^^ C) = ((S ^^ C) ^^ (H ^^ (true && D))) := by decide
      exact b4 _ _ _ _

theorem testBit_toNat_shl (b : Bool) (k q : ℕ) :
    (Nat.shiftLeft b.toNat k).testBit q = (b && decide (q = k)) := by
  change (b.toNat <<< k).testBit q = _
  rw [Nat.testBit_shiftLeft, Trace6091.testBit_toNat]
  by_cases h : q = k
  · subst h
    simp
  · by_cases h2 : q ≥ k
    · simp [h2, h, show q - k ≠ 0 by omega]
    · simp [h2, h]

theorem bmT_nat {i : ℕ} (hi : i < 12) : bmT i = bmaskN i := by
  rw [Trace6091.bmT_eq i hi, ← CFSG.Monster.B.Rep4371.native_bmaskN]

theorem wordT_nat (a : ℕ) : wordT a = wordN a := by
  rw [Trace6091.wordT_eq, ← CFSG.Monster.B.Rep4371.native_wordN]

theorem testBit_triTab (a : ℕ) {i j : ℕ} (hi : i < 12) (hj : j < 12) :
    (triTab a).testBit (12 * i + j) = parN 24 (wordN a &&& (bmaskN i &&& bmaskN j)) := by
  unfold triTab
  refine (testBit_orLoop' (fun i' => Nat.rec (motive := fun _ => ℕ) 0 (fun j acc2 => Nat.lor acc2
      (Nat.shiftLeft (par24 (Nat.land (wordT a) (Nat.land (bmT i') (bmT j)))) (Nat.add (Nat.mul 12 i') j))) 12)
    _ 12).trans ?_
  have hin : ∀ i', (Nat.rec (motive := fun _ => ℕ) 0 (fun j acc2 => Nat.lor acc2
      (Nat.shiftLeft (par24 (Nat.land (wordT a) (Nat.land (bmT i') (bmT j)))) (Nat.add (Nat.mul 12 i') j))) 12 :
        ℕ).testBit (12 * i + j) = true ↔ ∃ j' < 12, (Nat.shiftLeft (par24 (Nat.land (wordT a)
          (Nat.land (bmT i') (bmT j')))) (Nat.add (Nat.mul 12 i') j')).testBit (12 * i + j) = true :=
    fun i' => Trace6091.testBit_orLoop (fun j => Nat.shiftLeft (par24 (Nat.land (wordT a)
      (Nat.land (bmT i') (bmT j)))) (Nat.add (Nat.mul 12 i') j)) (12 * i + j) 12
  have hp : ∀ i' j', par24 (Nat.land (wordT a) (Nat.land (bmT i') (bmT j'))) =
      (xorSum (Nat.land (wordT a) (Nat.land (bmT i') (bmT j'))).testBit 24).toNat := by
    intro i' j'
    rw [Trace6091.par24_eq, CFSG.Monster.B.Rep4371.native_xorSum]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨i', hi', h⟩
    rw [hin] at h
    obtain ⟨j', hj', h⟩ := h
    rw [hp, testBit_toNat_shl, Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : i' = i := by simp only [nadd, nmul] at h2; omega
    have e2 : j' = j := by simp only [nadd, nmul] at h2; omega
    subst e1 e2
    rw [parN_xorSum, ← h1, Benes.nland, Benes.nland, wordT_nat, bmT_nat hi, bmT_nat hj]
  · intro h
    refine ⟨i, hi, ?_⟩
    rw [hin]
    refine ⟨j, hj, ?_⟩
    rw [hp, testBit_toNat_shl, decide_eq_true (by simp only [nadd, nmul]), Bool.and_true,
      Benes.nland, Benes.nland, wordT_nat, bmT_nat hi, bmT_nat hj, ← parN_xorSum]
    exact h

theorem testBit_halfTab (a : ℕ) {i : ℕ} (hi : i < 12) :
    (halfTab a).testBit i = decide (popcN 24 (wordN a &&& bmaskN i) / 2 % 2 = 1) := by
  unfold halfTab
  refine (testBit_orLoop' (fun i' => Nat.shiftLeft (Nat.land (Nat.shiftRight (popc24 (Nat.land (wordT a)
    (bmT i'))) 1) 1) i') _ 12).trans ?_
  have hv : ∀ i', Nat.land (Nat.shiftRight (popc24 (Nat.land (wordT a) (bmT i'))) 1) 1 =
      (decide (popcN 24 (wordT a &&& bmT i') / 2 % 2 = 1)).toNat := by
    intro i'
    rw [KeysOKAux.popc24_eq, Benes.nland, Benes.nland, Benes.nshr, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
    rcases Nat.mod_two_eq_zero_or_one (popcN 24 (wordT a &&& bmT i') / 2) with h | h <;> simp [h]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨i', hi', h⟩
    rw [hv, testBit_toNat_shl, Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨h1, h2⟩ := h
    rw [decide_eq_true_iff] at h2
    subst h2
    rw [wordT_nat, bmT_nat hi] at h1
    exact decide_eq_true h1
  · intro h
    refine ⟨i, hi, ?_⟩
    rw [hv, testBit_toNat_shl, decide_eq_true rfl, Bool.and_true, wordT_nat, bmT_nat hi]
    exact h

theorem kN_eq (a c : ℕ) : kN a c = decide (popcN 24 (wordN a &&& wordN c) / 2 % 2 = 1) := by
  unfold kN
  cases h : popcN 24 (wordN a &&& wordN c) / 2 % 2 == 1 <;> simp_all

theorem ble_t {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := by rw [Nat.ble_eq]; exact h

theorem ble_f {a b : ℕ} (h : b < a) : Nat.ble a b = false := by
  rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; omega

theorem pi0N_xor_even' {m a : ℕ} (h : m.testBit 0 = false) : pi0N (m ^^^ a) = m ^^^ pi0N a := by
  unfold pi0N
  rw [Nat.testBit_xor, h, Bool.false_xor, Nat.xor_assoc]

theorem div_two_xor' (m a : ℕ) : (2 * m ^^^ a) / 2 = m ^^^ a / 2 := by
  have := Nat.shiftRight_xor_distrib (a := 2 * m) (b := a) (i := 1)
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one] at this
  rw [this, Nat.mul_div_cancel_left _ (by decide)]

theorem pi0N_lt' {a : ℕ} (ha : a < 4096) : pi0N a < 4096 := by
  unfold pi0N
  have : (if a.testBit 0 = true then 63 else 0) < 2 ^ 12 := by split_ifs <;> decide
  exact Nat.xor_lt_two_pow (n := 12) ha this

theorem rowNew_sign {a r : ℕ} (ha : a < 4096) (hr : r < 4096) :
    rowNewOf (eYN a) r = if 2048 ≤ r then r else r ^^^ (pi0N a / 2) := by
  unfold rowNewOf eYN Native.rowEta
  by_cases h : 2048 ≤ r
  · rw [decide_eq_true h, if_pos rfl, if_pos h]
    simp only
    rw [pi0N_rowC]
    unfold Native.rowIdx
    rw [pi0N_rowC]
    unfold Native.rowC
    simp only [if_true]
    omega
  · rw [decide_eq_false h, if_neg (by decide), if_neg h, pi0N_rowC]
    unfold Native.rowIdx shiftN
    simp only [Bool.false_eq_true, if_false, Nat.zero_add]
    rw [pi0N_pi0N, pi0N_xor_even' (rowC_even r)]
    unfold Native.rowC
    rw [div_two_xor', Nat.mod_eq_of_lt (b := 2048) (by omega : r < 2048)]
    have h1 : r < 2 ^ 11 := by simp only [Nat.reducePow]; omega
    have h2 : pi0N a / 2 < 2 ^ 11 := by have := pi0N_lt' ha; simp only [Nat.reducePow]; omega
    exact Nat.mod_eq_of_lt (by simpa using Nat.xor_lt_two_pow h1 h2)

theorem testBit_rowNewS {a r : ℕ} (ha : a < 4096) (hr : r < 4096) (k : ℕ) :
    (rowNewOf (eYN a) r).testBit k = (r.testBit k ^^ (!decide (2048 ≤ r) && (pi0N a / 2).testBit k)) := by
  rw [rowNew_sign ha hr]
  by_cases h : 2048 ≤ r
  · rw [if_pos h, decide_eq_true h]
    simp
  · rw [if_neg h, decide_eq_false h, Nat.testBit_xor]
    simp

theorem tS_eq (a : ℕ) : Nat.shiftRight (Nat.xor a (selB (Nat.land a 1) 63)) 1 = pi0N a / 2 := by
  have e : Nat.land a 1 = (a.testBit 0).toNat := by
    rw [Benes.nland, Nat.and_one_is_mod, mod2_toNat]
  rw [e, selB_toNat', Benes.nshr, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rfl

@[expose] noncomputable def selWS (a b : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (idPlane SX b)
    (Nat.xor (idPlane SX b) (selB (bitN (Nat.shiftRight (Nat.xor a (selB (Nat.land a 1) 63)) 1) (Nat.sub b 5))
      (Nat.xor (ones SX) (idPlane SX 16))))
    (andB (Nat.ble 5 b) (Nat.blt b 16))

@[expose] noncomputable def LWS (a : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc
    (Nat.shiftLeft (mux SX valW (selWS a b) (idPlane SX b)) (Nat.mul b SX))) 17

@[expose] noncomputable def sgWS (a : ℕ) : ℕ :=
  Nat.xor (colMask SX (wordT a)) (mux SX (idPlane SX 16)
    (Nat.xor (quadPl SX (triTab a) rowCodeP) (parSel SX (halfTab a) rowCodeP))
    (parSel SX a (thetaPl SX rowCodeP)))

theorem monoSignWOK_eq (a : ℕ) (E : MonoE) : monoSignWOK a E =
    andB (eqOn SX 17 valW (monoW 17 E (LWS a)) (idP 17)) (Nat.beq E.sgW (Nat.land valW (sgWS a))) := rfl

theorem sign_labW {a : ℕ} (ha : a < 4096) :
    ∀ p < SX, p % 32 < 24 → Holds 17 SX (LWS a) p (32 * rowNewOf (eYN a) (p / 32) + p % 32) := by
  intro p hp hm b hb
  have hpw : valW.testBit p = true := by rw [testBit_valW, decide_eq_true ⟨hp, hm⟩]
  have hr : p / 32 < 4096 := by have : SX = 131072 := rfl; omega
  have hpe : p = 32 * (p / 32) + p % 32 := (Nat.div_add_mod p 32).symm
  unfold LWS
  refine (testBit_muxLoop valW_lt _ _ hb hp).trans ?_
  rw [hpw, if_pos rfl, testBit_32mul _ (by omega)]
  unfold selWS
  have hpb : p.testBit b = if b < 5 then (p % 32).testBit b else (p / 32).testBit (b - 5) := by
    conv_lhs => rw [hpe]
    exact testBit_32mul _ (by omega) b
  by_cases h5 : b < 5
  · rw [ListAux.blt_t (by omega : b < 16), ble_f h5]
    change (idPlane SX b).testBit p = _
    rw [idPlane_SX hb, decide_eq_true hp, Bool.true_and, hpb, if_pos h5, if_pos h5]
  · rw [if_neg h5, testBit_rowNewS ha hr]
    have h16 : p.testBit 16 = decide (2048 ≤ p / 32) := rowEta_bit hp
    by_cases hb16 : b < 16
    · rw [ble_t (by omega : 5 ≤ b), ListAux.blt_t hb16]
      change (Nat.xor (idPlane SX b) (selB (bitN (Nat.shiftRight (Nat.xor a (selB (Nat.land a 1) 63)) 1)
        (Nat.sub b 5)) (Nat.xor (ones SX) (idPlane SX 16)))).testBit p = _
      rw [nxor, Nat.testBit_xor, idPlane_SX hb, decide_eq_true hp, Bool.true_and, testBit_selB_bitN,
        tS_eq, nxor, Nat.testBit_xor, testBit_ones, decide_eq_true hp, idPlane_SX (by norm_num),
        decide_eq_true hp, Bool.true_and, h16, hpb, if_neg h5]
      cases decide (2048 ≤ p / 32) <;> cases (pi0N a / 2).testBit (Nat.sub b 5) <;> rfl
    · rw [ble_t (by omega : 5 ≤ b), ListAux.blt_f (by omega : 16 ≤ b)]
      change (idPlane SX b).testBit p = _
      have hb' : b = 16 := by omega
      subst hb'
      have ht : (pi0N a / 2).testBit (16 - 5) = false := by
        have := pi0N_lt' ha
        exact bit_hi (n := 11) (by simp only [Nat.reducePow]; omega) (by norm_num)
      rw [idPlane_SX hb, decide_eq_true hp, Bool.true_and, ht, Bool.and_false, Bool.xor_false, hpb,
        if_neg h5]

theorem testBit_colMask {K m p : ℕ} (hK : 5 ≤ K) (hm : m < 2 ^ 32) :
    (colMask (2 ^ K) m).testBit p = (decide (p < 2 ^ K) && m.testBit (p % 32)) := by
  unfold colMask
  rw [Benes.nmul, Benes.repU_eq]
  have hW : (2 : ℕ) ^ K = 32 * (Nat.div (2 ^ K) 32) := by
    rw [Benes.ndiv, show (32 : ℕ) = 2 ^ 5 from rfl, Nat.mul_div_cancel' (Nat.pow_dvd_pow 2 hK)]
  rw [← hW]
  exact Benes.testBit_mul_div (L := 32) (n := Nat.div (2 ^ K) 32) (by decide) hW hm p

theorem bmask_lt : ∀ i < 12, bmaskN i < 2 ^ 24 := by decide +kernel

theorem wordN_lt (a : ℕ) : wordN a < 2 ^ 24 :=
  lt_of_bits fun k hk => by
    unfold wordN at hk
    rw [testBit_combN] at hk
    by_contra hc
    rw [xorSum_congr (g := fun _ => false) (fun i hi => by
      rw [bit_hi (bmask_lt i hi) (by omega), Bool.and_false])] at hk
    rw [xorSum_false] at hk
    exact absurd hk (by decide)

theorem sign_sgW {a : ℕ} {p : ℕ} (hp : p < SX) :
    (sgWS a).testBit p = ((wordN a).testBit (p % 32) ^^
      (eYN a (Native.rowEta (p / 32)) (Native.rowC (p / 32))).1) := by
  have hwl : wordT a < 2 ^ 32 := by
    rw [wordT_nat]
    have h1 := wordN_lt a
    have h2 : (2 : ℕ) ^ 24 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
    exact lt_of_lt_of_le h1 h2
  have hcm : (colMask SX (wordT a)).testBit p = (wordN a).testBit (p % 32) := by
    have := testBit_colMask (K := 17) (m := wordT a) (p := p) (by norm_num) hwl
    rw [← SX_eq, decide_eq_true hp, Bool.true_and] at this
    rw [this, wordT_nat]
  have hrc := holds_rowCode hp
  unfold sgWS
  rw [nxor, Nat.testBit_xor, hcm, testBit_mux hp, idPlane_SX (by norm_num), decide_eq_true hp,
    Bool.true_and, rowEta_bit hp]
  unfold eYN
  rw [pi0N_rowC]
  cases Native.rowEta (p / 32)
  · simp only [Bool.false_eq_true, if_false]
    rw [parSel_holds hp (holds_thetaPl hp hrc)]
    rfl
  · simp only [if_true]
    rw [nxor, Nat.testBit_xor, testBit_quadPl hp hrc, parSel_holds hp hrc, kN_eq]
    rw [show wordN (Native.rowC (p / 32)) = combN bmaskN 12 (Native.rowC (p / 32)) from rfl,
      (half_weight a (Native.rowC (p / 32)) 12 le_rfl).2, pairN_xs]
    have hQ : xorSum (fun i => xorSum (fun j => decide (i < j) && (Native.rowC (p / 32)).testBit i &&
        (Native.rowC (p / 32)).testBit j && (triTab a).testBit (12 * i + j)) 12) 12 =
        xorSum (fun i => xorSum (fun j => decide (i < j) && (Native.rowC (p / 32)).testBit i &&
        (Native.rowC (p / 32)).testBit j && parN 24 (wordN a &&& (bmaskN i &&& bmaskN j))) 12) 12 :=
      xorSum_congr fun i hi => xorSum_congr fun j hj => by rw [testBit_triTab a hi hj]
    have hH : xorSum (fun i => (halfTab a).testBit i && (Native.rowC (p / 32)).testBit i) 12 =
        xorSum (fun i => (Native.rowC (p / 32)).testBit i &&
          decide (popcN 24 (wordN a &&& bmaskN i) / 2 % 2 = 1)) 12 :=
      xorSum_congr fun i hi => by rw [testBit_halfTab a hi, Bool.and_comm]
    rw [hQ, hH]

theorem signG_get {a j c : ℕ} (hj : j < 24) (hc : c < 24) :
    (Native.signG a)[j * 24 + c]! = if j = c then sgnI ((wordN a).testBit j) else 0 := by
  unfold Native.signG
  rw [getElem!_pos (Array.ofFn _) (j * 24 + c) (by simp; omega), Array.getElem_ofFn]
  have e1 : (j * 24 + c) / 24 = j := by omega
  have e2 : (j * 24 + c) % 24 = c := by omega
  simp only [e1, e2]
  by_cases h : j = c
  · subst h
    simp
  · simp [h]

theorem monoG_sign (a : ℕ) :
    MonoG (Native.GD.ofGen (Native.mkCtx ()) (.sign a)) (fun j => j) (fun j => (wordN a).testBit j) where
  lt _ h := h
  inj _ _ _ _ h := h
  get j hj c hc := by
    have hGG : (Native.GD.ofGen (Native.mkCtx ()) (.sign a)).G = Native.signG a := by
      simp only [Native.GD.ofGen]
    rw [hGG]
    exact signG_get hj hc

theorem sign_W {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {a : ℕ} (ha : a < 4096) {E : MonoE}
    (hNets : monoNetsOK E = true) (hW : monoSignWOK a E = true)
    {v : Native.DVec} {W : ℕ}
    (hW1 : ∀ r < 4096, ∀ j < 24, resPN n SX W (32 * r + j) = resN n v (98580 + 24 * r + j))
    (hW2 : ∀ p < SX, 24 ≤ p % 32 → resPN n SX W p = 0) (hW3 : W < 2 ^ (n * SX)) :
    (∀ r < 4096, ∀ j < 24, resPN n SX (monoW n E (negMN SX n E.sgW W)) (32 * r + j) =
      resN n (Native.applyGen (Native.mkCtx ()) (.sign a) v) (98580 + 24 * r + j)) ∧
    (∀ p < SX, 24 ≤ p % 32 → resPN n SX (monoW n E (negMN SX n E.sgW W)) p = 0) ∧
      monoW n E (negMN SX n E.sgW W) < 2 ^ (n * SX) := by
  obtain ⟨π, hP⟩ := pg_monoW hNets
  have hSX : SX = 131072 := rfl
  have hrlt : ∀ r < 4096, rowNewOf (eYN a) r < 4096 := fun r _ => rowIdx_lt _ _
  rw [monoSignWOK_eq, andB_eq, Bool.and_eq_true, Nat.beq_eq] at hW
  obtain ⟨hchk, hsgc⟩ := hW
  have hvb : ∀ p, valW.testBit p = true ↔ p < SX ∧ p % 32 < 24 := fun p => by
    rw [testBit_valW, decide_eq_true_iff]
  obtain ⟨part1, part2⟩ := labels_pi (k := 17) SX_eq hP valW_lt
    (fun p => 32 * rowNewOf (eYN a) (p / 32) + p % 32) hchk
    (fun p hp hm => sign_labW ha p hp ((hvb p).1 hm).2)
    (fun p hp hm b hb => by
      refine (testBit_muxLoop valW_lt _ _ hb hp).trans ?_
      rw [hm, if_neg (by decide), idPlane_SX hb, decide_eq_true hp, Bool.true_and])
    (fun p hp hm => by
      have hm' := ((hvb p).1 hm).2
      have h1 := hrlt (p / 32) (by omega)
      refine ⟨by omega, (hvb _).2 ⟨by omega, by omega⟩⟩)
  have hsrc : ∀ x, x < SX → x % 32 < 24 → π x < SX ∧ π x % 32 < 24 ∧
      32 * rowNewOf (eYN a) (π x / 32) + π x % 32 = x := by
    intro x hx hm
    obtain ⟨h1, h2⟩ := part1 x hx ((hvb x).2 ⟨hx, hm⟩)
    exact ⟨hP.g.lt x hx, ((hvb _).1 h1).2, h2⟩
  have hrsurj : ∀ r' < 4096, ∃ r < 4096, rowNewOf (eYN a) r = r' := by
    intro r' hr'
    obtain ⟨h1, h2, h3⟩ := hsrc (32 * r') (by omega) (by omega)
    exact ⟨π (32 * r') / 32, by omega, by omega⟩
  have hrinj := inj_of_surj hrlt hrsurj
  have hπ : ∀ r < 4096, ∀ c < 24, π (32 * rowNewOf (eYN a) r + (fun j => j) c) = 32 * r + c := by
    intro r hr c hc
    have h0 := hrlt r hr
    obtain ⟨h1, h2, h3⟩ := hsrc (32 * rowNewOf (eYN a) r + c) (by omega) (by omega)
    have e3 := hrinj _ (by omega) _ hr (by omega : rowNewOf (eYN a)
      (π (32 * rowNewOf (eYN a) r + c) / 32) = rowNewOf (eYN a) r)
    simp only
    omega
  have hpad : ∀ x < SX, 24 ≤ x % 32 → 24 ≤ π x % 32 := by
    intro x hx hm
    have := part2 (fun p hp p' hp' hm1 hm2 e => by
      have a1 := ((hvb p).1 hm1).2
      have a2 := ((hvb p').1 hm2).2
      beta_reduce at e
      have c1 := hrlt (p / 32) (by omega)
      have c2 := hrlt (p' / 32) (by omega)
      have e2 := hrinj _ (by omega) _ (by omega) (by omega : rowNewOf (eYN a) (p / 32) =
        rowNewOf (eYN a) (p' / 32))
      omega) x hx (by
        cases h : valW.testBit x
        · rfl
        · exact absurd ((hvb x).1 h).2 (by omega))
    by_contra hc
    exact absurd ((hvb _).2 ⟨hP.g.lt x hx, by omega⟩) (by rw [this]; decide)
  have hsg : ∀ r < 4096, ∀ c < 24, E.sgW.testBit (32 * r + c) =
      ((eYN a (Native.rowEta r) (Native.rowC r)).1 ^^ (fun j => (wordN a).testBit j) c) := by
    intro r hr c hc
    rw [hsgc, nland, Nat.testBit_and, (hvb _).2 ⟨by omega, by omega⟩, Bool.true_and,
      sign_sgW (by omega), show (32 * r + c) / 32 = r by omega, show (32 * r + c) % 32 = c by omega,
      Bool.xor_comm]
  have hgW : (Native.GD.ofGen (Native.mkCtx ()) (.sign a)).rowT = Native.monoRows (eYN a) := by
    simp only [Native.GD.ofGen]
  have hl0 : (Native.GD.ofGen (Native.mkCtx ()) (.sign a)).latS = 0 := by simp only [Native.GD.ofGen]
  have hr0 : (Native.GD.ofGen (Native.mkCtx ()) (.sign a)).rowS = 0 := by simp only [Native.GD.ofGen]
  exact moveW_sound hn hlg hNets hP hl0 hr0 hgW (monoG_sign a) (fun r _ => rfl) hrlt hrinj hπ hpad
    hsg hW1 hW2 hW3

@[expose] noncomputable def rowLoopS (a : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (bitN (wordT a) i) (Nat.mul 32 i))) 24

theorem monoSignAOK_eq (a : ℕ) (E : MonoE) : monoSignAOK a E =
    andB (Nat.beq (amapN 10 E.cn (idP 10)) (idP 10))
      (Nat.beq E.sgA (Nat.land valA (Nat.xor (colMask SA (wordT a)) (Nat.mul (rowLoopS a) (ones 32))))) :=
  rfl

theorem rowCopy (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (f i).toNat (Nat.mul 32 i))) n <
        2 ^ (32 * n) ∧
      Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (f i).toNat (Nat.mul 32 i))) n *
        (2 ^ 32 - 1) < 2 ^ (32 * n) ∧
      ∀ i j, j < 32 → (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc
        (Nat.shiftLeft (f i).toNat (Nat.mul 32 i))) n * (2 ^ 32 - 1)).testBit (32 * i + j) =
          (decide (i < n) && f i)
  | 0 => ⟨by simp, by simp, fun i j _ => by simp⟩
  | n + 1 => by
    obtain ⟨hR, hM, hb⟩ := rowCopy f n
    have hs : Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc
        (Nat.shiftLeft (f i).toNat (Nat.mul 32 i))) (n + 1) = Nat.lor (Nat.rec (motive := fun _ => ℕ) 0
          (fun i acc => Nat.lor acc (Nat.shiftLeft (f i).toNat (Nat.mul 32 i))) n)
        (Nat.shiftLeft (f n).toNat (Nat.mul 32 n)) := rfl
    rw [hs]
    generalize Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc
      (Nat.shiftLeft (f i).toNat (Nat.mul 32 i))) n = R at hR hM hb ⊢
    have ht : (f n).toNat ≤ 1 := by cases f n <;> decide
    have hK : (f n).toNat * (2 ^ 32 - 1) ≤ 2 ^ 32 - 1 := by
      have := Nat.mul_le_mul_right (2 ^ 32 - 1) ht
      omega
    have e1 : Nat.lor R (Nat.shiftLeft (f n).toNat (Nat.mul 32 n)) = 2 ^ (32 * n) * (f n).toNat + R := by
      rw [Benes.nlor, Nat.or_comm, Benes.nmul, Benes.nshl, ← Nat.shiftLeft_add_eq_or_of_lt hR,
        Nat.shiftLeft_eq, Nat.mul_comm]
    rw [e1]
    have e2 : (2 ^ (32 * n) * (f n).toNat + R) * (2 ^ 32 - 1) =
        2 ^ (32 * n) * ((f n).toNat * (2 ^ 32 - 1)) + R * (2 ^ 32 - 1) := by ring
    have hp : (2 : ℕ) ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
    have h32 : (1 : ℕ) ≤ 2 ^ 32 - 1 := by decide
    refine ⟨?_, ?_, fun i j hj => ?_⟩
    · have h3 : 2 ^ (32 * n) * ((f n).toNat + 1) ≤ 2 ^ (32 * n) * 2 ^ 32 :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at h3
      omega
    · rw [e2]
      have hKl : (f n).toNat * (2 ^ 32 - 1) < 2 ^ 32 :=
        lt_of_le_of_lt hK (Nat.sub_lt (Nat.two_pow_pos 32) Nat.one_pos)
      have h3 : 2 ^ (32 * n) * ((f n).toNat * (2 ^ 32 - 1) + 1) ≤ 2 ^ (32 * n) * 2 ^ 32 :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hKl)
      rw [Nat.mul_succ] at h3
      omega
    · rw [e2, Nat.testBit_two_pow_mul_add _ hM]
      have hKl : (f n).toNat * (2 ^ 32 - 1) < 2 ^ 32 :=
        lt_of_le_of_lt hK (Nat.sub_lt (Nat.two_pow_pos 32) Nat.one_pos)
      split_ifs with hi
      · have hin : i < n := by omega
        rw [hb i j hj, decide_eq_true hin, decide_eq_true (by omega : i < n + 1)]
      · rcases Nat.lt_or_ge n i with h | h
        · have : 32 * i + j - 32 * n ≥ 32 := by omega
          rw [bit_hi hKl this, decide_eq_false (by omega)]
          simp
        · have hin : i = n := by omega
          subst hin
          rw [show 32 * i + j - 32 * i = j by omega, decide_eq_true (by omega)]
          cases f i
          · simp
          · simp only [Bool.toNat_true, Nat.one_mul, Nat.testBit_two_pow_sub_one, Bool.true_and]
            exact decide_eq_true hj

theorem sign_A {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {a : ℕ} {E : MonoE}
    (hNets : monoNetsOK E = true) (hAA : monoSignAOK a E = true)
    {v : Native.DVec} {A : ℕ}
    (hA1 : ∀ i < 24, ∀ j < 24, resPN n SA A (32 * i + j) = resN n v (Native.aIdx i j))
    (hA2 : ∀ p < SA, (24 ≤ p % 32 ∨ 24 ≤ p / 32) → resPN n SA A p = 0) (hA3 : A < 2 ^ (n * SA)) :
    (∀ i < 24, ∀ j < 24, resPN n SA (amapN n E.cn (negMN SA n E.sgA A)) (32 * i + j) =
      resN n (Native.applyGen (Native.mkCtx ()) (.sign a) v) (Native.aIdx i j)) ∧
    (∀ p < SA, (24 ≤ p % 32 ∨ 24 ≤ p / 32) → resPN n SA (amapN n E.cn (negMN SA n E.sgA A)) p = 0) ∧
      amapN n E.cn (negMN SA n E.sgA A) < 2 ^ (n * SA) := by
  obtain ⟨π, hP⟩ := pg_amapN hNets
  have hSA : SA = 1024 := rfl
  rw [monoSignAOK_eq, andB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hAA
  obtain ⟨hid, hsgc⟩ := hAA
  have hπid : ∀ x < SA, π x = x := by
    intro x hx
    have hpx := hP.g.lt x hx
    have h1 : Holds 10 SA (idP 10) (π x) x := fun b hb => by
      have := hP.g.bit 10 (idP 10) b x hb hx
      rw [hid, Bool.not_false, Bool.true_and] at this
      rw [← this]
      exact testBit_idP (k := 10) hb hx
    have h2 : Holds 10 SA (idP 10) (π x) (π x) := fun b hb => testBit_idP (k := 10) hb hpx
    exact holds_eq h2 h1 hpx hx
  have hπ : ∀ i < 24, ∀ j < 24, π (32 * (fun j => j) i + (fun j => j) j) = 32 * i + j :=
    fun i _ j _ => by
      beta_reduce
      exact hπid _ (by omega)
  have hpad : ∀ x < SA, (24 ≤ x % 32 ∨ 24 ≤ x / 32) → (24 ≤ π x % 32 ∨ 24 ≤ π x / 32) :=
    fun x hx h => by rw [hπid x hx]; exact h
  have hwl : wordT a < 2 ^ 32 := by
    rw [wordT_nat]
    have h1 := wordN_lt a
    have h2 : (2 : ℕ) ^ 24 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
    exact lt_of_lt_of_le h1 h2
  have hsg : ∀ i < 24, ∀ j < 24, E.sgA.testBit (32 * i + j) =
      ((fun j => (wordN a).testBit j) i ^^ (fun j => (wordN a).testBit j) j) := by
    intro i hi j hj
    have hcm := testBit_colMask (K := 10) (m := wordT a) (p := 32 * i + j) (by norm_num) hwl
    rw [← SA_eq] at hcm
    have hrow := (rowCopy (fun i => (wordT a).testBit i) 24).2.2 i j (by omega)
    rw [hsgc, nland, Nat.testBit_and, testBit_valA, decide_eq_true ⟨by omega, by omega, by omega⟩,
      Bool.true_and, nxor, Nat.testBit_xor, hcm, decide_eq_true (by omega), Bool.true_and,
      show (32 * i + j) % 32 = j by omega, Benes.nmul, Benes.ones_eq]
    unfold rowLoopS
    simp only [bitN_eq_toNat]
    rw [hrow, decide_eq_true hi, Bool.true_and, wordT_nat, Bool.xor_comm]
  have hl0 : (Native.GD.ofGen (Native.mkCtx ()) (.sign a)).latS = 0 := by simp only [Native.GD.ofGen]
  exact moveA_sound hn hlg hNets hP hl0 (monoG_sign a) hπ hpad hsg hA1 hA2 hA3

theorem sign_parts {F : Fix} {a : ℕ} {E : MonoE} (hE : monoEntOK F [a] E = true) :
    monoNetsOK E = true ∧ monoPadOK E = true ∧ a < 4096 ∧ monoSignXOK F a E = true ∧
      monoSignWOK a E = true ∧ monoSignAOK a E = true := by
  change andB (andB (monoNetsOK E) (monoPadOK E)) (monoSignOK F a E) = true at hE
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hE
  obtain ⟨⟨hN, hP⟩, hS⟩ := hE
  unfold monoSignOK at hS
  rw [andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at hS
  exact ⟨hN, hP, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2⟩

theorem sign_L_lt (F : Fix) (hK : KeyBind F) (a : ℕ) : Nat.xor (T1S F a) (Dd1S F a) < 2 ^ (12 * SX) := by
  have h6 : ∀ m, m < 2 ^ SX → repP SX 6 m < 2 ^ (12 * SX) := fun m hm =>
    lt_of_lt_of_le (repP_lt hm 6) (Nat.pow_le_pow_right (by decide) (by omega))
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hK.la (h6 _ (parSel_lt _ _ _)))
    (Nat.xor_lt_two_pow (constP_lt _ _ _ (parSel_lt _ _ _)) (h6 _ ?_))
  exact Nat.xor_lt_two_pow (by rw [KeysOKAux.pT_eq]; exact selB_toNat_lt (parSel_lt _ _ _))
    (parSel_lt _ _ _)

theorem sign_hL {F : Fix} (hK : KeyBind F) (a : ℕ) :
    ∀ p < SX, ∀ b < 24, (Nat.lor (Nat.xor (T1S F a) (Dd1S F a))
        (Nat.shiftLeft (Nat.xor (T2S F a) (Dd2S F a)) (Nat.mul 12 SX))).testBit (b * SX + p) =
      if b < 12 then (imgS a (pv SX F.keyA p) (pv SX F.keyD p)).1.testBit b
      else (imgS a (pv SX F.keyA p) (pv SX F.keyD p)).2.testBit (b - 12) := by
  intro p hp b hb
  obtain ⟨-, -, h1, -, h2, h3⟩ := sign_bits (F := F) a hp
  have hm : ∀ x k, k < 12 → (x % 4096).testBit k = x.testBit k := fun x k hk => by
    rw [show (4096 : ℕ) = 2 ^ 12 from rfl, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and]
  rw [testBit_split12 (sign_L_lt F hK a) hp]
  have e1 : ∀ x y z : ℕ, (imgS a x y).1 = (x ^^^ (if thetaBit a x then 63 else 0) ^^^ daS a y) % 4096 ∧
      (imgS a x y).2 = (acodeN a x ^^^ ((if pairN 63 y then thetaN a else 0) ^^^ y)) % 4096 :=
    fun _ _ _ => ⟨rfl, rfl⟩
  by_cases h : b < 12
  · rw [if_pos h, if_pos h, (e1 _ _ 0).1, hm _ _ h]
    exact h1 b h
  · rw [if_neg h, if_neg h, (e1 _ _ 0).2, hm _ _ (by omega)]
    exact holds_xor h2 h3 (b - 12) (by omega)

theorem sign_hsg {F : Fix} (hK : KeyBind F) (hG : KeysGood) {a : ℕ} {E : MonoE}
    (hsgc : E.sgX = Nat.land validX (Nat.xor (Nat.xor (T0S F a) (Dd0S F a)) (parP SX (Dd1S F a) (T2S F a))))
    {q : ℕ} (hq : q < 98280) : E.sgX.testBit (xposK q) = sgS a (keyQ q).1 (keyQ q).2 := by
  have hxq := InitAux.xposK_lt' hq
  obtain ⟨hO, hPd, -, h4, h5, -⟩ := sign_bits (F := F) a hxq
  obtain ⟨ka, kd⟩ := pv_key hK hG hq
  rw [hsgc, nland, Nat.testBit_and, InitAux.xposK_mem hq, Bool.true_and, nxor, Nat.testBit_xor, nxor,
    Nat.testBit_xor, testBit_parP hxq h4 h5]
  unfold T0S Dd0S
  rw [parSel_holds hxq (holds_thetaPl hxq (holds_pv SX F.keyA _)), nland, Nat.testBit_and, nxor,
    Nat.testBit_xor, testBit_ones, decide_eq_true hxq, hO, hPd, ka, kd]
  unfold sgS thetaBit
  cases pairN 63 (keyQ q).2 <;> rfl

end MonoAux

open MonoAux in
theorem monoPerm_sound {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {F : Fix} (hK : KeyBind F)
    (hG : KeysGood) {arr : Array ℕ} (hsz : arr.size = 24) {E : MonoE}
    (hE : monoEntOK F (arrList arr) E = true) {v : Native.DVec} {t : St} (ht : RepN n v t) (f : Bool) :
    Native.permValid arr = true ∧
      RepN n (Native.applyGen (Native.mkCtx ()) (.perm arr) v) (f, monoStepN n E t.2.1 t.2.2.1 t.2.2.2) := by
  obtain ⟨hNets, hPad, hv, hA, hX, hW, hAA⟩ := perm_parts hsz hE
  obtain ⟨tX1, tX2, tX3, tA1, tA2, tA3, tW1, tW2, tW3⟩ := ht
  rw [monoPermXOK_eq] at hX
  rw [andB_eq, Bool.and_eq_true] at hX
  obtain ⟨hchk, hsg⟩ := hX
  rw [Nat.beq_eq] at hchk hsg
  obtain ⟨x1, x2, x3⟩ := moveX_sound hn hlg hK hG hNets hPad (imgP arr) (imgP_lt arr) (imgP_zero arr)
    (perm_hL hA F) hchk (fun a _ => kappaN arr a)
    (fun q hq => by rw [hsg, quad_kappa hA (InitAux.xposK_lt' hq) (fun b hb => hK.ka q hq b hb)])
    (fun p hp => xT_perm hG hv hp) tX1 tX2 tX3
  obtain ⟨w1, w2, w3⟩ := perm_W hn hlg hA hNets hW tW1 tW2 tW3
  obtain ⟨a1, a2, a3⟩ := perm_A hn hlg hA hNets hAA tA1 tA2 tA3
  exact ⟨hv, x1, x2, x3, a1, a2, a3, w1, w2, w3⟩

open MonoAux in
theorem monoSign_sound {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {F : Fix} (hK : KeyBind F)
    (hG : KeysGood) {a : ℕ} {E : MonoE} (hE : monoEntOK F [a] E = true) {v : Native.DVec} {t : St}
    (ht : RepN n v t) (f : Bool) :
    RepN n (Native.applyGen (Native.mkCtx ()) (.sign a) v) (f, monoStepN n E t.2.1 t.2.2.1 t.2.2.2) := by
  obtain ⟨hNets, hPad, ha, hX, hW, hAA⟩ := sign_parts hE
  obtain ⟨tX1, tX2, tX3, tA1, tA2, tA3, tW1, tW2, tW3⟩ := ht
  rw [monoSignXOK_eq, andB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hX
  obtain ⟨hchk, hsgc⟩ := hX
  obtain ⟨x1, x2, x3⟩ := moveX_sound hn hlg hK hG hNets hPad (imgS a) (imgS_lt a) (imgS_zero a)
    (sign_hL hK a) hchk (sgS a) (fun q hq => sign_hsg hK hG hsgc hq)
    (fun p hp => xT_sign hG ha hp) tX1 tX2 tX3
  obtain ⟨w1, w2, w3⟩ := sign_W hn hlg ha hNets hW tW1 tW2 tW3
  obtain ⟨a1, a2, a3⟩ := sign_A hn hlg hNets hAA tA1 tA2 tA3
  exact ⟨x1, x2, x3, a1, a2, a3, w1, w2, w3⟩

end CFSG.KC.KStep

end
