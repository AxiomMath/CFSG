module

public import CFSG.Certificates.Kernel.P0RankK.VisTab
public import CFSG.Certificates.Kernel.P0RankK.VisBits
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.P0Vis

open CFSG.KC.P0Orb CFSG.Monster.B.TwoA.Sp8.P0Rank MonsterB.P0Rank

structure LiftPm (dat : Data) (ds ks : List ℕ) (X : ℕ → ℕ) : Prop where
  lt16 : ∀ j < ks.length, X j < 2 ^ 16
  lt9 : ∀ i < ds.length, X (ks.length + i) < 2 ^ 9
  sq : ∀ j < ks.length,
    X j ^^^ actK dat.aCols (ks.getD j 0) (X j) = fval dat (4 * ks.getD j 0)
  comm : ∀ j k, j < k → k < ks.length →
    (X j ^^^ actK dat.aCols (ks.getD k 0) (X j)) ^^^
      (X k ^^^ actK dat.aCols (ks.getD j 0) (X k)) =
      fval dat (1 + 4 * ks.getD j 0 + 4096 * ks.getD k 0)
  conj : ∀ i < ds.length, ∀ j < ks.length,
    betaN dat.beta (X j) (ds.getD i 0) ^^^
      (X (ks.length + i) ^^^ actK dat.uConjT (ks.getD j 0) (X (ks.length + i))) =
      fval dat (2 + 4 * ks.getD j 0 + 4096 * ds.getD i 0)

theorem key_bits (kind κ x : ℕ) (hk : kind < 4) (hκ : κ < 1024) :
    Nat.land (kind + 4 * κ + 4096 * x) 3 = kind ∧
      Nat.land (Nat.shiftRight (kind + 4 * κ + 4096 * x) 2) 1023 = κ ∧
      Nat.shiftRight (kind + 4 * κ + 4096 * x) 12 = x := by
  have e3 : ∀ n : ℕ, Nat.land n 3 = n % 4 := fun n => Nat.and_two_pow_sub_one_eq_mod n 2
  have e1023 : ∀ n : ℕ, Nat.land n 1023 = n % 1024 := fun n => Nat.and_two_pow_sub_one_eq_mod n 10
  have es : ∀ n k : ℕ, Nat.shiftRight n k = n / 2 ^ k := fun n k => Nat.shiftRight_eq_div_pow n k
  rw [e3, e1023, es, es]
  norm_num
  omega

theorem fval_sq (dat : Data) {κ : ℕ} (hκ : κ < 1024) :
    fval dat (4 * κ) = (pmul dat (uK κ) (uK κ)).1.1 := by
  obtain ⟨h1, h2, -⟩ := key_bits 0 κ 0 (by omega) hκ
  simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h1 h2
  unfold fval
  simp only [h1, h2]
  rfl

theorem fval_comm (dat : Data) {κ : ℕ} (hκ : κ < 1024) (x : ℕ) :
    fval dat (1 + 4 * κ + 4096 * x) =
      (lmul dat.beta (pmul dat (uK κ) (uK x)).1 (linv dat.beta (pmul dat (uK x) (uK κ)).1)).1 := by
  obtain ⟨h1, h2, h3⟩ := key_bits 1 κ x (by omega) hκ
  unfold fval
  simp only [h1, h2, h3]
  rfl

theorem fval_conj (dat : Data) {κ : ℕ} (hκ : κ < 1024) (x : ℕ) :
    fval dat (2 + 4 * κ + 4096 * x) = (conjkap dat κ (x, 0)).2 := by
  obtain ⟨h1, h2, h3⟩ := key_bits 2 κ x (by omega) hκ
  unfold fval
  simp only [h1, h2, h3]
  rfl

theorem lc_succ' (f : ℕ → ℕ) (x : ℕ) : ∀ n, lc f x (n + 1) =
    (if x.testBit 0 then f 0 else 0) ^^^ lc (fun e => f (e + 1)) (x / 2) n
  | 0 => by simp [lc]
  | n + 1 => by
    rw [lc, lc_succ' f x n, lc, Nat.testBit_div_two, Nat.xor_assoc]

theorem lc_zero_x (f : ℕ → ℕ) : ∀ n, lc f 0 n = 0
  | 0 => rfl
  | n + 1 => by simp [lc, lc_zero_x f n]

theorem pAct_zero_x (w m : ℕ) : ∀ n p, pAct w m n p 0 = 0
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem lc_xor_fun (g h : ℕ → ℕ) (x : ℕ) : ∀ n,
    lc (fun e => g e ^^^ h e) x n = lc g x n ^^^ lc h x n
  | 0 => by simp [lc]
  | n + 1 => by
    rw [lc, lc, lc, lc_xor_fun g h x n]
    split_ifs
    · ac_rfl
    · simp

theorem lc_two_pow (x : ℕ) : ∀ n, lc (fun e => 1 <<< e) x n = x % 2 ^ n
  | 0 => by simp [lc, Nat.mod_one]
  | n + 1 => by
    rw [lc, lc_two_pow x n]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    split_ifs with hb
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hi : i < n
      · simp [hi, show i < n + 1 by omega, show n ≠ i by omega]
      · by_cases hin : i = n
        · subst hin
          simp [hb]
        · simp [hi, show ¬ i < n + 1 by omega, Ne.symm hin]
    · rw [Nat.zero_testBit, Bool.xor_false]
      by_cases hi : i < n
      · simp [hi, show i < n + 1 by omega]
      · by_cases hin : i = n
        · subst hin
          simp [hb]
        · simp [hi, show ¬ i < n + 1 by omega]

theorem lc_fld (w m : ℕ) : ∀ n p x, lc (fun e => fld p (w * e) m) x n = pAct w m n p x
  | 0, _, _ => rfl
  | n + 1, p, x => by
    rw [lc_succ', pAct_succ]
    have hf : (fun e => fld p (w * (e + 1)) m) = fun e => fld (p >>> w) (w * e) m := by
      funext e
      simp only [fld]
      change p >>> (w * (e + 1)) &&& m = p >>> w >>> (w * e) &&& m
      rw [← Nat.shiftRight_add, Nat.mul_succ, Nat.add_comm]
    rw [hf, lc_fld w m n (p >>> w) (x / 2)]
    by_cases hx : x = 0
    · subst hx
      simp [pAct_zero_x]
    · have hb : Nat.beq x 0 = false := by
        cases h : Nat.beq x 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hx
      have e1 : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
      have e2 : Nat.shiftRight x 1 = x / 2 := by
        change x >>> 1 = x / 2
        rw [Nat.shiftRight_eq_div_pow, pow_one]
      rw [hb, e1, e2, cond_false, Nat.testBit_zero]
      have hp : fld p (w * 0) m = Nat.land p m := by
        simp only [fld, Nat.mul_zero]
        rfl
      rw [hp]
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · rw [h]
        rfl
      · rw [h]
        rfl

theorem lc_one_xor (w m p x n : ℕ) (hx : x < 2 ^ n) :
    lc (fun e => 1 <<< e ^^^ fld p (w * e) m) x n = x ^^^ pAct w m n p x := by
  rw [lc_xor_fun, lc_two_pow, Nat.mod_eq_of_lt hx, lc_fld]

def evS (X : ℕ → ℕ) (P : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => evS X P n ^^^ par16 (fld P (16 * n + 1) 65535 &&& X n)

def ev (X : ℕ → ℕ) (N P : ℕ) : ℕ := (P &&& 1) ^^^ evS X P N

theorem fld_xor (a b o m : ℕ) : fld (a ^^^ b) o m = fld a o m ^^^ fld b o m := by
  change (a ^^^ b) >>> o &&& m = (a >>> o &&& m) ^^^ (b >>> o &&& m)
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]

theorem evS_xor (X : ℕ → ℕ) (a b : ℕ) : ∀ n, evS X (a ^^^ b) n = evS X a n ^^^ evS X b n
  | 0 => by simp [evS]
  | n + 1 => by
    rw [evS, evS, evS, evS_xor X a b n, fld_xor, Nat.and_xor_distrib_right, par16_xor]
    ac_rfl

theorem ev_xor (X : ℕ → ℕ) (N a b : ℕ) : ev X N (a ^^^ b) = ev X N a ^^^ ev X N b := by
  rw [ev, ev, ev, evS_xor, Nat.and_xor_distrib_right]
  ac_rfl

theorem evS_eq_zero (X : ℕ → ℕ) (P : ℕ) (h : ∀ v, fld P (16 * v + 1) 65535 = 0) :
    ∀ n, evS X P n = 0
  | 0 => rfl
  | n + 1 => by rw [evS, evS_eq_zero X P h n, h n, Nat.zero_and, par16_zero]; rfl

theorem ev_small (X : ℕ → ℕ) (N : ℕ) {r : ℕ} (hr : r < 2) : ev X N r = r := by
  have h : ∀ v, fld r (16 * v + 1) 65535 = 0 := by
    intro v
    change r >>> (16 * v + 1) &&& 65535 = 0
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (lt_of_lt_of_le hr
      (by calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ (16 * v + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.zero_and]
  rw [ev, evS_eq_zero X r h, Nat.xor_zero]
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;> rfl

theorem ev_one (X : ℕ → ℕ) (N : ℕ) : ev X N 1 = 1 := ev_small X N (by norm_num)

theorem testBit_ge16 {T : ℕ} (hT : T < 2 ^ 16) {i : ℕ} (hi : 16 ≤ i) : T.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) hi))

theorem fld_shl {T : ℕ} (hT : T < 2 ^ 16) (j v : ℕ) :
    fld (T <<< (16 * j + 1)) (16 * v + 1) 65535 = if v = j then T else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (T <<< (16 * j + 1) >>> (16 * v + 1) &&& (2 ^ 16 - 1)).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  split_ifs with hv
  · subst hv
    by_cases hi : i < 16
    · simp [hi, show 16 * v + 1 + i - (16 * v + 1) = i by omega]
    · simp [hi, testBit_ge16 hT (by omega : 16 ≤ i)]
  · rw [Nat.zero_testBit]
    by_cases hi : i < 16
    · rcases Nat.lt_or_gt_of_ne hv with hlt | hgt
      · simp [hi, show ¬ 16 * j + 1 ≤ 16 * v + 1 + i by omega]
      · simp [testBit_ge16 hT (by omega : 16 ≤ 16 * v + 1 + i - (16 * j + 1))]
    · simp [hi]

theorem evS_shl (X : ℕ → ℕ) {T : ℕ} (hT : T < 2 ^ 16) (j : ℕ) :
    ∀ n, evS X (T <<< (16 * j + 1)) n = if j < n then par16 (T &&& X j) else 0
  | 0 => by simp [evS]
  | n + 1 => by
    rw [evS, evS_shl X hT j n, fld_shl hT]
    by_cases hjn : j = n
    · subst hjn
      simp [Nat.lt_irrefl]
    · rw [if_neg (Ne.symm hjn), Nat.zero_and, par16_zero, Nat.xor_zero]
      by_cases h : j < n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

theorem ev_shl (X : ℕ → ℕ) {N T j : ℕ} (hT : T < 2 ^ 16) (hj : j < N) :
    ev X N (T <<< (16 * j + 1)) = par16 (T &&& X j) := by
  have h0 : T <<< (16 * j + 1) &&& 1 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]
    cases i with
    | zero => simp
    | succ i => simp [Nat.testBit_succ]
  rw [ev, h0, evS_shl X hT j N, if_pos hj, Nat.zero_xor]

theorem ev_foldl (X : ℕ → ℕ) (N : ℕ) (f : Blk → ℕ) :
    ∀ (bl : List Blk) (acc : ℕ), (∀ b ∈ bl, ev X N (f b) = 0) →
      ev X N (bl.foldl (fun acc b => acc ^^^ f b) acc) = ev X N acc
  | [], _, _ => rfl
  | b :: bl, acc, h => by
    rw [List.foldl_cons, ev_foldl X N f bl _ (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')),
      ev_xor, h b List.mem_cons_self, Nat.xor_zero]

theorem xor_cancel4 (a b : ℕ) : a ^^^ b ^^^ a ^^^ b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.zero_testBit]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem par16_land_xor (K a b : ℕ) : par16 (K &&& (a ^^^ b)) = par16 (K &&& a) ^^^ par16 (K &&& b) := by
  rw [Nat.and_xor_distrib_left, par16_xor]

theorem blkVal_zero (AT BT BC FC : ℕ) (ds ks : List ℕ) (j k iF K : ℕ) :
    blkVal AT BT BC FC ds ks (0, j, k, iF, K) =
      par16 (K &&& fld FC (16 * iF) 65535) ^^^
        tA (fld AT (256 * ks.getD j 0) m256) K <<< (16 * j + 1) := rfl

theorem blkVal_one (AT BT BC FC : ℕ) (ds ks : List ℕ) (j k iF K : ℕ) :
    blkVal AT BT BC FC ds ks (1, j, k, iF, K) =
      par16 (K &&& fld FC (16 * iF) 65535) ^^^
        tA (fld AT (256 * ks.getD k 0) m256) K <<< (16 * j + 1) ^^^
        tA (fld AT (256 * ks.getD j 0) m256) K <<< (16 * k + 1) := rfl

theorem blkVal_two (AT BT BC FC : ℕ) (ds ks : List ℕ) (j k iF K : ℕ) :
    blkVal AT BT BC FC ds ks (2, j, k, iF, K) =
      par16 (K &&& fld FC (16 * iF) 65535) ^^^
        tBeta (pAct 144 m144 16 BC (ds.getD k 0)) K <<< (16 * j + 1) ^^^
        tB (fld BT (96 * ks.getD j 0) m96) K <<< (16 * (ks.length + k) + 1) := rfl

theorem par16_tA (p K : ℕ) {x : ℕ} (hx : x < 2 ^ 16) :
    par16 (tA p K &&& x) = par16 (K &&& (x ^^^ pAct 16 65535 16 p x)) := by
  rw [← lc_one_xor 16 65535 p x 16 hx]
  exact (par16_land_lc _ K x 16 le_rfl).symm

theorem par16_tB (p K : ℕ) {x : ℕ} (hx : x < 2 ^ 9) :
    par16 (tB p K &&& x) = par16 (K &&& (x ^^^ pAct 9 511 9 p x)) := by
  rw [← lc_one_xor 9 511 p x 9 hx]
  exact (par16_land_lc _ K x 9 (by norm_num)).symm

theorem par16_tBeta (P K x : ℕ) :
    par16 (tBeta P K &&& x) = par16 (K &&& pAct 9 511 16 P x) := by
  rw [← lc_fld 9 511 16 P x]
  exact (par16_land_lc _ K x 16 le_rfl).symm

theorem getD_mem {l : List ℕ} {j : ℕ} (hj : j < l.length) : l.getD j 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

section Sound

variable {dat : Data} {AT BT BC FK FC : ℕ} {ds ks : List ℕ}
  (hA : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, aAct AT κ x = actK dat.aCols κ x)
  (hB : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 9, bAct BT κ x = actK dat.uConjT κ x)
  (hβ : ∀ x < 2 ^ 16, ∀ y < 2 ^ 16, bet BC x y = betaN dat.beta x y)
  (hFC : ∀ i, fld FC (16 * i) 65535 = fval dat (fld FK (32 * i) m32))
  (hks : ∀ κ ∈ ks, κ < 2 ^ 10) (hds : ∀ δ ∈ ds, δ < 2 ^ 16)
include hA hB hβ hFC hks hds

theorem ev_blkVal {X : ℕ → ℕ} (hX : LiftPm dat ds ks X) {b : Blk}
    (hb : blkKey FK ds ks b = true) :
    ev X (ks.length + ds.length) (blkVal AT BT BC FC ds ks b) = 0 := by
  obtain ⟨kind, j, k, iF, K⟩ := b
  have htA : ∀ p, tA p K < 2 ^ 16 := fun p => tr_lt _ K 16
  have htB : ∀ p, tB p K < 2 ^ 16 := fun p => lt_of_lt_of_le (tr_lt _ K 9) (by norm_num)
  have htβ : ∀ p, tBeta p K < 2 ^ 16 := fun p => tr_lt _ K 16
  rcases kind with _ | _ | _ | n
  ·
    change (Nat.blt j ks.length && Nat.beq (fld FK (32 * iF) m32) (4 * ks.getD j 0)) = true at hb
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
    obtain ⟨hj, hkey⟩ := hb
    rw [blkVal_zero, ev_xor, ev_small X _ (par16_lt _), ev_shl X (htA _) (by omega),
      par16_tA _ K (hX.lt16 j hj)]
    change _ ^^^ par16 (K &&& (X j ^^^ aAct AT (ks.getD j 0) (X j))) = 0
    rw [hA _ (hks _ (getD_mem hj)) _ (hX.lt16 j hj), hX.sq j hj, hFC, hkey, Nat.xor_self]
  ·
    change (Nat.blt j ks.length && (Nat.blt j k && Nat.blt k ks.length &&
      Nat.beq (fld FK (32 * iF) m32) (1 + 4 * ks.getD j 0 + 4096 * ks.getD k 0))) = true at hb
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
    obtain ⟨hj, ⟨hjk, hk⟩, hkey⟩ := hb
    rw [blkVal_one, ev_xor, ev_xor, ev_small X _ (par16_lt _),
      ev_shl X (htA _) (by omega), ev_shl X (htA _) (by omega),
      par16_tA _ K (hX.lt16 j hj), par16_tA _ K (hX.lt16 k hk)]
    change _ ^^^ par16 (K &&& (X j ^^^ aAct AT (ks.getD k 0) (X j))) ^^^
      par16 (K &&& (X k ^^^ aAct AT (ks.getD j 0) (X k))) = 0
    rw [hA _ (hks _ (getD_mem hk)) _ (hX.lt16 j hj), hA _ (hks _ (getD_mem hj)) _ (hX.lt16 k hk),
      hFC, hkey, ← hX.comm j k hjk hk, par16_land_xor]
    exact xor_cancel4 _ _
  ·
    change (Nat.blt j ks.length && (Nat.beq 2 2 && Nat.blt k ds.length &&
      Nat.beq (fld FK (32 * iF) m32) (2 + 4 * ks.getD j 0 + 4096 * ds.getD k 0))) = true at hb
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
    obtain ⟨hj, ⟨-, hk⟩, hkey⟩ := hb
    have hν := hX.lt9 k hk
    rw [blkVal_two, ev_xor, ev_xor, ev_small X _ (par16_lt _),
      ev_shl X (htβ _) (by omega), ev_shl X (htB _) (by omega),
      par16_tBeta, par16_tB _ K hν]
    change _ ^^^ par16 (K &&& bet BC (X j) (ds.getD k 0)) ^^^
      par16 (K &&& (X (ks.length + k) ^^^ bAct BT (ks.getD j 0) (X (ks.length + k)))) = 0
    rw [hβ _ (hX.lt16 j hj) _ (hds _ (getD_mem hk)), hB _ (hks _ (getD_mem hj)) _ hν,
      hFC, hkey, ← hX.conj k hk j hj, par16_land_xor]
    exact xor_cancel4 _ _
  ·
    change (Nat.blt j ks.length && (Nat.beq (n + 3) 2 && Nat.blt k ds.length &&
      Nat.beq (fld FK (32 * iF) m32) (2 + 4 * ks.getD j 0 + 4096 * ds.getD k 0))) = true at hb
    simp only [Bool.and_eq_true, Nat.beq_eq] at hb
    omega

theorem farkOK_sound {bl : List Blk} (h : farkOK AT BT BC FK FC ds ks bl = true) (X : ℕ → ℕ) :
    ¬ LiftPm dat ds ks X := by
  intro hX
  rw [farkOK, Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] at h
  have hz := ev_foldl X (ks.length + ds.length) (blkVal AT BT BC FC ds ks) bl 0
    (fun b hb => ev_blkVal hA hB hβ hFC hks hds hX (h.1 b hb))
  have h2 : bl.foldl (fun acc b => acc ^^^ blkVal AT BT BC FC ds ks b) 0 = 1 := h.2
  rw [h2, ev_one, ev_small X _ (by norm_num : (0 : ℕ) < 2)] at hz
  exact absurd hz (by decide)

end Sound

theorem cfgsOK_spec {AT BT BC FK FC : ℕ} {ds g : List ℕ} :
    ∀ (cfgs : List Cfg) (φ : ℕ), cfgsOK AT BT BC FK FC ds g φ cfgs = true →
      ∀ t (ht : t < cfgs.length), (∀ x ∈ cfgs[t].1, par16 (Nat.land (φ + t) x) = 0) ∧
        farkOK AT BT BC FK FC ds (cfgs[t].1.map (lAct g)) cfgs[t].2 = true
  | [], _, _, t, ht => absurd ht (by simp)
  | c :: cs, φ, h, t, ht => by
    rw [cfgsOK, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h
    cases t with
    | zero =>
      refine ⟨fun x hx => ?_, h.1.2⟩
      exact Nat.eq_of_beq_eq_true (h.1.1 x hx)
    | succ t =>
      have := cfgsOK_spec cs (φ + 1) h.2 t (by simpa using ht)
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using this

theorem ble_false {x y : ℕ} (h : y < x) : Nat.ble x y = false := by
  cases hb : Nat.ble x y
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) (by omega)

theorem bit_of_land {M κ : ℕ} (h : Nat.beq (Nat.land (Nat.shiftRight M κ) 1) 1 = true) :
    M.testBit κ = true := by
  have h1 : (M >>> κ) &&& 1 = 1 := Nat.eq_of_beq_eq_true h
  rw [Nat.and_one_is_mod] at h1
  rw [Nat.shiftRight_eq_div_pow] at h1
  rw [Nat.testBit_eq_decide_div_mod_eq, h1]
  rfl

theorem candOK_sound {AT BT BC FK FC : ℕ} {ds : List ℕ} {a M' nM' : ℕ} {c : Cand}
    (h : candOK AT BT BC FK FC ds a M' nM' c = true) :
    (∀ κ ∈ c.1, M'.testBit κ = true) ∧ a * nM' ≤ 65536 ∧
      ∀ φ < (if a * nM' ≤ 32768 then 1 else 2 ^ c.1.length), ∃ (cs : List ℕ) (bl : List Blk),
        (∀ x ∈ cs, par16 (Nat.land φ x) = 0) ∧
          farkOK AT BT BC FK FC ds (cs.map (lAct c.1)) bl = true := by
  rw [candOK] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hn, hg⟩, hlen⟩, hcf⟩ := h
  have key : a * nM' ≤ 65536 ∧
      c.2.length = (if a * nM' ≤ 32768 then 1 else 2 ^ c.1.length) := by
    by_cases h1 : a * nM' ≤ 32768
    · rw [Nat.ble_eq_true_of_le h1, cond_true] at hn hlen
      exact ⟨by omega, by rw [if_pos h1]; exact Nat.eq_of_beq_eq_true hlen⟩
    · rw [ble_false (x := a * nM') (y := 32768) (by omega), cond_false] at hn hlen
      by_cases h2 : a * nM' ≤ 65536
      · rw [Nat.ble_eq_true_of_le h2, cond_true] at hn hlen
        exact ⟨h2, by rw [if_neg h1]; exact Nat.eq_of_beq_eq_true hlen⟩
      · rw [ble_false (x := a * nM') (y := 65536) (by omega), cond_false] at hn
        exact absurd hn (by decide)
  refine ⟨fun κ hκ => bit_of_land (hg κ hκ), key.1, ?_⟩
  intro φ hφ
  have hlenφ : φ < c.2.length := by
    rw [key.2]
    exact hφ
  obtain ⟨h1, h2⟩ := cfgsOK_spec c.2 0 hcf φ hlenφ
  exact ⟨c.2[φ].1, c.2[φ].2, fun x hx => by simpa using h1 x hx, h2⟩

theorem lAct_lt {w : ℕ} : ∀ (g : List ℕ), (∀ κ ∈ g, κ < 2 ^ w) → ∀ x, lAct g x < 2 ^ w
  | [], _, _ => Nat.two_pow_pos w
  | κ :: g, h, x => by
    change Nat.xor (bif Nat.beq (Nat.land x 1) 1 then κ else 0) (lAct g (Nat.shiftRight x 1)) < _
    refine Nat.xor_lt_two_pow ?_ (lAct_lt g (fun κ' hκ' => h κ' (List.mem_cons_of_mem _ hκ')) _)
    cases Nat.beq (Nat.land x 1) 1
    · exact Nat.two_pow_pos w
    · exact h κ List.mem_cons_self

set_option exponentiation.threshold 1024 in
theorem cand_noSol {dat : Data} {AT BT BC FK FC : ℕ} {ds : List ℕ} {a M' nM' : ℕ} {c : Cand}
    (hA : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, aAct AT κ x = actK dat.aCols κ x)
    (hB : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 9, bAct BT κ x = actK dat.uConjT κ x)
    (hβ : ∀ x < 2 ^ 16, ∀ y < 2 ^ 16, bet BC x y = betaN dat.beta x y)
    (hFC : ∀ i, fld FC (16 * i) 65535 = fval dat (fld FK (32 * i) m32))
    (hds : ∀ δ ∈ ds, δ < 2 ^ 16) (hM' : M' < 2 ^ 1024)
    (h : candOK AT BT BC FK FC ds a M' nM' c = true) :
    (∀ κ ∈ c.1, M'.testBit κ = true) ∧ a * nM' ≤ 65536 ∧
      ∀ φ < (if a * nM' ≤ 32768 then 1 else 2 ^ c.1.length), ∃ cs : List ℕ,
        (∀ x ∈ cs, par16 (Nat.land φ x) = 0) ∧ ∀ X, ¬ LiftPm dat ds (cs.map (lAct c.1)) X := by
  obtain ⟨hg, ha, hφ⟩ := candOK_sound h
  have hg10 : ∀ κ ∈ c.1, κ < 2 ^ 10 := by
    intro κ hκ
    by_contra hc
    have hk : 1024 ≤ κ := Nat.le_of_not_lt hc
    have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hM' (Nat.pow_le_pow_right Nat.zero_lt_two hk))
    rw [hg κ hκ] at this
    exact Bool.noConfusion this
  refine ⟨hg, ha, fun φ hφ' => ?_⟩
  obtain ⟨cs, bl, hcs, hf⟩ := hφ φ hφ'
  refine ⟨cs, hcs, fun X => farkOK_sound hA hB hβ hFC ?_ hds hf X⟩
  intro κ hκ
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hκ
  exact lAct_lt c.1 hg10 x

end CFSG.KC.P0Vis

end
