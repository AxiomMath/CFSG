module

public import Certificates.Data.Kernel.StdOdd.ChainP
public import CFSG.Certificates.Kernel.StdOdd.ChainSound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Algebra.Group.Submonoid.Membership
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.StdOdd.ChainP

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KC.StdOdd.ChainP CFSG.KS.StdOdd.Orbit
  CFSG.KS.StdOdd.Chain

@[expose] def Bd (U : List ℕ) : Prop := ∀ c, nthN U c < 2 ^ 156

theorem full156 : full 156 = 2 ^ 156 - 1 := by decide

theorem packP_nil : packP [] = 0 := rfl

theorem packP_cons (x : ℕ) (U : List ℕ) : packP (x :: U) = 2 ^ 156 * packP U + x := by
  change x + packP U <<< 156 = _
  rw [Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm]

theorem Bd.tail {x : ℕ} {U : List ℕ} (h : Bd (x :: U)) : Bd U := fun c => h (c + 1)

theorem Bd.head {x : ℕ} {U : List ℕ} (h : Bd (x :: U)) : x < 2 ^ 156 := h 0

theorem bd_nil : Bd [] := fun c => by rw [nthN_nil]; positivity

theorem testBit_packP : ∀ (U : List ℕ), Bd U → ∀ p,
    (packP U).testBit p = (nthN U (p / 156)).testBit (p % 156)
  | [], _, p => by rw [packP_nil, nthN_nil, Nat.zero_testBit, Nat.zero_testBit]
  | x :: U, h, p => by
    rw [packP_cons, Nat.testBit_two_pow_mul_add _ h.head]
    split_ifs with hp
    · rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp, nthN_cons_zero]
    · have e1 : p / 156 = (p - 156) / 156 + 1 := by omega
      have e2 : p % 156 = (p - 156) % 156 := by omega
      rw [e1, e2, nthN_cons_succ]
      exact testBit_packP U h.tail (p - 156)

theorem packP_mul : ∀ (L : List ℕ) (x : ℕ), x * packP L = packP (L.map (x * ·))
  | [], x => by rw [List.map_nil, packP_nil, Nat.mul_zero]
  | y :: L, x => by
    rw [List.map_cons, packP_cons, packP_cons, ← packP_mul L x]
    ring

theorem nthN_replicate (x : ℕ) : ∀ n c, nthN (List.replicate n x) c = if c < n then x else 0
  | 0, c => by simp [nthN_nil]
  | n + 1, 0 => by simp [List.replicate_succ, nthN_cons_zero]
  | n + 1, c + 1 => by
    rw [List.replicate_succ, nthN_cons_succ, nthN_replicate x n c]
    simp

theorem c0P_eq : c0P = packP (List.replicate 156 1) := Nat.eq_of_beq_eq_true (by quickRfl)

theorem one_testBit' (j : ℕ) : (1 : ℕ).testBit j = decide (j = 0) := by
  rw [← Nat.pow_zero 2, Nat.testBit_two_pow]
  simp [eq_comm]

theorem ite_testBit (q : Prop) [Decidable q] (x j : ℕ) :
    (if q then x else 0).testBit j = (decide q && x.testBit j) := by
  split_ifs with h <;> simp [h]

theorem testBit_rep {x : ℕ} (hx : x < 2 ^ 156) (p : ℕ) :
    (x * c0P).testBit p = (decide (p / 156 < 156) && x.testBit (p % 156)) := by
  have hb : Bd (List.replicate 156 x) := fun c => by
    rw [nthN_replicate]
    split_ifs
    · exact hx
    · positivity
  rw [c0P_eq, packP_mul, List.map_replicate, Nat.mul_one, testBit_packP _ hb, nthN_replicate,
    ite_testBit]

theorem testBit_c0P (p : ℕ) :
    c0P.testBit p = (decide (p / 156 < 156) && decide (p % 156 = 0)) := by
  have := testBit_rep (x := 1) (by decide) p
  rw [Nat.one_mul, one_testBit'] at this
  exact this

@[expose] def selL (M : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => (if M.testBit 0 then 1 else 0) :: selL (M >>> 156) n

theorem nthN_selL : ∀ n M c, nthN (selL M n) c = if c < n ∧ M.testBit (156 * c) = true then 1 else 0
  | 0, M, c => by simp [selL, nthN_nil]
  | n + 1, M, 0 => by simp [selL, nthN_cons_zero]
  | n + 1, M, c + 1 => by
    rw [selL, nthN_cons_succ, nthN_selL n (M >>> 156) c, Nat.testBit_shiftRight]
    have e : 156 + 156 * c = 156 * (c + 1) := by ring
    rw [e]
    simp

theorem bd_selL (M n : ℕ) : Bd (selL M n) := fun c => by
  rw [nthN_selL]
  split_ifs <;> norm_num

theorem land_c0P (M : ℕ) : M &&& c0P = packP (selL M 156) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, testBit_c0P, testBit_packP _ (bd_selL M 156), nthN_selL, ite_testBit,
    one_testBit']
  by_cases h2 : p % 156 = 0
  · have e : 156 * (p / 156) = p := by omega
    rw [e]
    by_cases h1 : p / 156 < 156 <;> simp [h1, h2]
  · simp [h2]

theorem nthN_map0 {f : ℕ → ℕ} (hf : f 0 = 0) : ∀ (L : List ℕ) c, nthN (L.map f) c = f (nthN L c)
  | [], c => by rw [List.map_nil, nthN_nil, hf]
  | x :: L, 0 => by rw [List.map_cons, nthN_cons_zero, nthN_cons_zero]
  | x :: L, c + 1 => by rw [List.map_cons, nthN_cons_succ, nthN_cons_succ, nthN_map0 hf L c]

theorem testBit_selMul (M : ℕ) {x : ℕ} (hx : x < 2 ^ 156) (p : ℕ) :
    ((M &&& c0P) * x).testBit p =
      (decide (p / 156 < 156 ∧ M.testBit (156 * (p / 156)) = true) && x.testBit (p % 156)) := by
  have hb : Bd ((selL M 156).map (x * ·)) := fun c => by
    rw [nthN_map0 (Nat.mul_zero x), nthN_selL]
    split_ifs
    · rw [Nat.mul_one]
      exact hx
    · rw [Nat.mul_zero]
      positivity
  rw [land_c0P, Nat.mul_comm, packP_mul, testBit_packP _ hb, nthN_map0 (Nat.mul_zero x), nthN_selL]
  split_ifs with h
  · rw [Nat.mul_one]
    simp [h]
  · rw [Nat.mul_zero, Nat.zero_testBit]
    simp [h]

theorem packP_land {U : List ℕ} (hU : Bd U) : packP U &&& full 156 = nthN U 0 := by
  rw [full156, Nat.and_two_pow_sub_one_eq_mod]
  cases U with
  | nil => rw [packP_nil, nthN_nil, Nat.zero_mod]
  | cons x U =>
    rw [packP_cons, nthN_cons_zero, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hU.head

theorem packP_shr {U : List ℕ} (hU : Bd U) : packP U >>> 156 = packP U.tail := by
  rw [Nat.shiftRight_eq_div_pow]
  cases U with
  | nil => rw [packP_nil, Nat.zero_div, List.tail_nil, packP_nil]
  | cons x U =>
    rw [packP_cons, List.tail_cons, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hU.head,
      Nat.add_zero]

theorem nthN_tail : ∀ (U : List ℕ) d, nthN U.tail d = nthN U (d + 1)
  | [], d => by rw [List.tail_nil, nthN_nil, nthN_nil]
  | x :: U, d => by rw [List.tail_cons, nthN_cons_succ]

theorem Bd.tail' {U : List ℕ} (h : Bd U) : Bd U.tail := fun c => by
  rw [nthN_tail]
  exact h (c + 1)

theorem mulPA_succ (c0 n M P acc : ℕ) : mulPA c0 (n + 1) M P acc =
    mulPA c0 n (M >>> 1) (P >>> 156) (acc ^^^ ((M &&& c0) * (P &&& full 156))) := by
  change forceN (Nat.xor acc (Nat.mul (Nat.land M c0) (Nat.land P (full 156))))
    (fun acc' => mulPA c0 n (Nat.shiftRight M 1) (Nat.shiftRight P 156) acc') = _
  rw [forceN_eq]
  rfl

theorem bz_and (a b : Bool) : bz (a && b) = bz a * bz b := by
  cases a <;> cases b <;> simp [bz]

theorem mulPA_bit : ∀ (n M : ℕ) (V : List ℕ) (acc p : ℕ), Bd V →
    bz ((mulPA c0P n M (packP V) acc).testBit p) = bz (acc.testBit p) +
      ∑ d ∈ Finset.range n, bz (decide (p / 156 < 156 ∧ M.testBit (156 * (p / 156) + d) = true)) *
        bz ((nthN V d).testBit (p % 156))
  | 0, M, V, acc, p, _ => by
    change bz (acc.testBit p) = _
    simp
  | n + 1, M, V, acc, p, hV => by
    rw [mulPA_succ, packP_shr hV, mulPA_bit n (M >>> 1) V.tail _ p hV.tail', Nat.testBit_xor,
      bz_xor, packP_land hV, testBit_selMul M (hV 0) p, bz_and, Finset.sum_range_succ']
    have e : ∀ d, (M >>> 1).testBit (156 * (p / 156) + d) =
        M.testBit (156 * (p / 156) + (d + 1)) := by
      intro d
      rw [Nat.testBit_shiftRight]
      congr 1
      omega
    simp only [e, nthN_tail, Nat.add_zero]
    ring

theorem rowA_lt : ∀ (PL : List ℕ) (r acc : ℕ), acc < 2 ^ 156 → Bd PL → rowA PL r acc < 2 ^ 156
  | [], _, acc, h, _ => h
  | P :: PL, r, acc, h, hP => by
    rw [rowA_cons]
    cases Nat.beq (r &&& 1) 0
    · exact rowA_lt PL _ _ (Nat.xor_lt_two_pow h hP.head) hP.tail
    · exact rowA_lt PL _ _ h hP.tail

theorem rowX_lt {PL : List ℕ} (hP : Bd PL) (r : ℕ) : rowX r PL < 2 ^ 156 := by
  rw [rowX_eq]
  exact rowA_lt PL r 0 (by positivity) hP

theorem mulP_bit {U : List ℕ} (hU : Bd U) (hl : lenN U = 156) (M p : ℕ) :
    (mulP c0P M (packP U)).testBit p =
      (decide (p / 156 < 156) && (rowX (M >>> (156 * (p / 156))) U).testBit (p % 156)) := by
  apply bz_inj
  rw [mulP, mulPA_bit 156 M U 0 p hU, Nat.zero_testBit, bz_and, rowX_eq, rowA_bit, hl,
    Nat.zero_testBit]
  by_cases hc : p / 156 < 156
  · simp only [hc, true_and, decide_true]
    simp [bz, Nat.testBit_shiftRight]
  · simp [hc, bz]

theorem shiftN_nil : ∀ c, shiftN [] c = []
  | 0 => rfl
  | c + 1 => by rw [shiftN, shiftN_nil c]; rfl

theorem shiftN_cons (M : ℕ) (Ms : List ℕ) :
    ∀ c, shiftN (M :: Ms) c = (M >>> (156 * c)) :: shiftN Ms c
  | 0 => by simp [shiftN]
  | c + 1 => by
    rw [shiftN, shiftN_cons M Ms c, shiftN]
    change (M >>> (156 * c) >>> 156) :: shiftRows (shiftN Ms c) = _
    rw [← Nat.shiftRight_add]
    rfl

theorem letP_bit {U : List ℕ} (hU : Bd U) (hl : lenN U = 156) : ∀ (Ms ms : List ℕ) (p : ℕ),
    (letP c0P (packP U) Ms ms).testBit p =
      (decide (p / 156 < 156) && (letterSum (shiftN Ms (p / 156)) ms U).testBit (p % 156))
  | [], ms, p => by
    rw [shiftN_nil]
    change (0 : ℕ).testBit p = (_ && (0 : ℕ).testBit _)
    simp
  | M :: Ms, [], p => by
    rw [shiftN_cons]
    change (0 : ℕ).testBit p = (_ && (0 : ℕ).testBit _)
    simp
  | M :: Ms, m :: ms, p => by
    rw [shiftN_cons]
    change ((((m &&& full 156) * c0P) &&& mulP c0P M (packP U)) ^^^
        letP c0P (packP U) Ms ms).testBit p =
      (_ && ((m &&& rowX (M >>> (156 * (p / 156))) U) ^^^
        letterSum (shiftN Ms (p / 156)) ms U).testBit (p % 156))
    have hm : m &&& full 156 < 2 ^ 156 := by
      rw [full156]
      exact Nat.and_lt_two_pow m (by omega)
    have hj : (full 156).testBit (p % 156) = true := by
      rw [full156, Nat.testBit_two_pow_sub_one]
      simp only [decide_eq_true_eq]
      omega
    rw [Nat.testBit_xor, Nat.testBit_and, testBit_rep hm, Nat.testBit_and, hj, mulP_bit hU hl,
      letP_bit hU hl Ms ms p, Nat.testBit_xor, Nat.testBit_and]
    cases decide (p / 156 < 156) <;> simp

theorem andNot_lt {x o : ℕ} (hx : x < 2 ^ 156) : andNot x o < 2 ^ 156 := by
  unfold andNot
  exact Nat.xor_lt_two_pow hx (Nat.lt_of_le_of_lt Nat.and_le_left hx)

theorem letterSum_lt {U : List ℕ} (hU : Bd U) : ∀ Ms ms : List ℕ, letterSum Ms ms U < 2 ^ 156
  | [], _ => by change (0 : ℕ) < _; positivity
  | _ :: _, [] => by change (0 : ℕ) < _; positivity
  | M :: Ms, m :: ms => by
    change (m &&& rowX M U) ^^^ letterSum Ms ms U < _
    exact Nat.xor_lt_two_pow (Nat.and_lt_two_pow m (rowX_lt hU M)) (letterSum_lt hU Ms ms)

theorem bd_stepL {U : List ℕ} (hU : Bd U) (hl : lenN U = 156) (Ms ms : List ℕ) :
    Bd (stepL Ms ms U) := fun c => by
  by_cases hc : c < 156
  · rw [stepL, stepAux_nth ms U _ U Ms c (by rw [hl]; exact hc)]
    exact Nat.xor_lt_two_pow (andNot_lt (hU c)) (letterSum_lt hU _ _)
  · rw [nthN_ge _ _ (by rw [lenN_stepL, hl]; omega)]
    positivity

theorem stepP_eq {U : List ℕ} (hU : Bd U) (hl : lenN U = 156) (Ms ms : List ℕ) :
    stepP c0P Ms ms (packP U) = packP (stepL Ms ms U) := by
  unfold stepP
  rw [forceN_eq]
  change (packP U ^^^ (packP U &&& ((orL ms &&& full 156) * c0P))) ^^^ letP c0P (packP U) Ms ms = _
  apply Nat.eq_of_testBit_eq
  intro p
  have ho : orL ms &&& full 156 < 2 ^ 156 := by
    rw [full156]
    exact Nat.and_lt_two_pow _ (by omega)
  have hj : (full 156).testBit (p % 156) = true := by
    rw [full156, Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]
    omega
  rw [testBit_packP _ (bd_stepL hU hl Ms ms), Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and,
    testBit_rep ho, Nat.testBit_and, hj, letP_bit hU hl, testBit_packP _ hU]
  by_cases hc : p / 156 < 156
  · rw [stepL, stepAux_nth ms U _ U Ms _ (by rw [hl]; exact hc), Nat.testBit_xor, andNot_testBit]
    cases (nthN U (p / 156)).testBit (p % 156) <;> cases (orL ms).testBit (p % 156) <;> simp [hc]
  · rw [nthN_ge (stepL Ms ms U) _ (by rw [lenN_stepL, hl]; omega), nthN_ge U _ (by rw [hl]; omega)]
    simp [hc]

@[expose] noncomputable def unpackA : ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => List.nil)
    (fun _ ih P => List.cons (Nat.land P (full 156)) (ih (Nat.shiftRight P 156)))

theorem unpackP_eq (P : ℕ) : unpackP P = unpackA 156 P := rfl

theorem unpackA_packP : ∀ (n : ℕ) (U : List ℕ), lenN U = n → Bd U → unpackA n (packP U) = U
  | 0, [], _, _ => rfl
  | 0, _ :: _, h, _ => by simp [lenN_cons] at h
  | n + 1, [], h, _ => by simp [lenN] at h
  | n + 1, x :: U, h, hU => by
    change (packP (x :: U) &&& full 156) :: unpackA n (packP (x :: U) >>> 156) = x :: U
    rw [packP_land hU, packP_shr hU, nthN_cons_zero, List.tail_cons,
      unpackA_packP n U (by rw [lenN_cons] at h; omega) hU.tail]

theorem bd_of_bdB : ∀ U : List ℕ, bdB U = true → Bd U
  | [], _ => bd_nil
  | x :: U, h => by
    change andB (Nat.blt x (Nat.shiftLeft 1 156)) (bdB U) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    intro c
    cases c with
    | zero =>
      rw [nthN_cons_zero]
      have := Nat.blt_eq.mp h.1
      rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul] at this
      exact this
    | succ c =>
      rw [nthN_cons_succ]
      exact bd_of_bdB U h.2 c

theorem walkP_eq {Ms : List ℕ} (k : List ℕ → Bool) : ∀ (S : List (List ℕ)) (U : List ℕ),
    Bd U → lenN U = 156 →
      walkP c0P Ms S (packP U) (fun P => forceLB (unpackP P) k) = walkK Ms S U k
  | [], U, hU, hl => by
    change forceLB (unpackP (packP U)) k = k U
    rw [forceLB_eq, unpackP_eq, unpackA_packP 156 U hl hU]
  | ms :: S, U, hU, hl => by
    change andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
        (forceB (stepP c0P Ms ms (packP U)) fun P =>
          walkP c0P Ms S P (fun P => forceLB (unpackP P) k)) =
      andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
        (forceLB (stepL Ms ms U) fun U => walkK Ms S U k)
    rw [forceB_eq, forceLB_eq, stepP_eq hU hl,
      walkP_eq k S _ (bd_stepL hU hl Ms ms) (by rw [lenN_stepL, hl])]

end CFSG.KS.StdOdd.ChainP

end
