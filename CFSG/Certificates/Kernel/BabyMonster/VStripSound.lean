module

public import CFSG.Certificates.Kernel.BabyMonster.Native.VStrip
public import CFSG.Certificates.Kernel.BabyMonster.StripLib
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.BM

open scoped Matrix

set_option exponentiation.threshold 8192

@[expose] noncomputable def vrow (r : Nat) : Fin 4370 → ZMod 2 :=
  fun j => if r.testBit (64 * j.val) then 1 else 0

@[expose] noncomputable def vecN (v : Nat) : Fin 4370 → ZMod 2 :=
  fun j => if v.testBit j.val then 1 else 0

@[expose] noncomputable def e0 : Fin 4370 → ZMod 2 := Pi.single 0 1

open CFSG.KC.BM.SL in
theorem vrow_rowOf (X t : Nat) (j : Fin 4370) :
    vrow (rowOf X t) j = bz (X.testBit (64 * j.val + t)) := by
  unfold vrow rowOf
  rw [nland, nshr, Nat.testBit_and, Nat.testBit_shiftRight, SM_eq, testBit_SMn_mul,
    decide_eq_true j.isLt, Bool.and_true, Nat.add_comm t]
  rfl

open CFSG.KC.BM.SL in
theorem mulS_rows {B : List Nat} (hB : wfMat B = true) (X : Nat) {t : Nat} (ht : t < 64) :
    vrow (rowOf (mulS B X) t) = vrow (rowOf X t) ᵥ* stripMat B := by
  rw [wfMat_eq] at hB
  funext j
  rw [vrow_rowOf, mulS_eq, mulSn_bit 4370 B X j.val t ht, (wf_bit hB).1, decide_eq_true j.isLt,
    bz_true, mul_one]
  simp only [Matrix.vecMul, dotProduct, vrow_rowOf, stripMat_eq, stripMatG_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => bz (X.testBit (64 * k + t)) *
    bz ((B.getD (k / 64) 0).testBit (64 * j.val + k % 64))) 4370]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
  intro k _ hk
  rw [Finset.mem_range, Nat.not_lt] at hk
  cases hb : (B.getD (k / 64) 0).testBit (64 * j.val + k % 64)
  · rw [bz_false, mul_zero]
  · have := wf_bit' hB (Nat.mod_lt _ (by norm_num)) hb
    omega

theorem forceB_eq (v : Nat) (k : Nat → Nat) : forceB v k = k v := by
  unfold forceB
  cases Nat.beq v 0 <;> rfl

theorem mulW_cons (B : List Nat) (Ws : List (List Nat)) (A : Nat) :
    mulW (B :: Ws) A = mulW Ws (mulS B A) := by
  change forceB (mulS B A) (mulW Ws) = mulW Ws (mulS B A)
  rw [forceB_eq]

theorem mulW_rows : ∀ {Ws : List (List Nat)}, (∀ W ∈ Ws, wfMat W = true) → ∀ (X : Nat) {t : Nat},
    t < 64 → vrow (rowOf (mulW Ws X) t) = vrow (rowOf X t) ᵥ* (Ws.map stripMat).prod
  | [], _, X, t, _ => by
    change vrow (rowOf X t) = vrow (rowOf X t) ᵥ* ([] : List _).prod
    rw [List.prod_nil, Matrix.vecMul_one]
  | B :: Ws, hW, X, t, ht => by
    rw [mulW_cons, mulW_rows (fun W hW' => hW W (List.mem_cons_of_mem _ hW')) _ ht,
      mulS_rows (hW B List.mem_cons_self) X ht, List.map_cons, List.prod_cons,
      Matrix.vecMul_vecMul]

theorem add_eq_xor_of_disj : ∀ (n a b : Nat), a < 2 ^ n → b < 2 ^ n →
    (∀ q, a.testBit q = true → b.testBit q = false) → a + b = a ^^^ b
  | 0, a, b, ha, hb, _ => by
    have : a = 0 := by omega
    have : b = 0 := by omega
    subst_vars
    rfl
  | n + 1, a, b, ha, hb, hd => by
    have ea : a = 2 ^ 1 * (a / 2) + a % 2 := by omega
    have eb : b = 2 ^ 1 * (b / 2) + b % 2 := by omega
    have hd2 : ∀ q, (a / 2).testBit q = true → (b / 2).testBit q = false := by
      intro q hq
      rw [← Nat.testBit_succ] at hq ⊢
      exact hd _ hq
    have ih := add_eq_xor_of_disj n (a / 2) (b / 2) (by rw [Nat.pow_succ] at ha; omega)
      (by rw [Nat.pow_succ] at hb; omega) hd2
    have h0 : a % 2 + b % 2 = a % 2 ^^^ b % 2 := by
      rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> rw [h1, h2]
      · rfl
      · rfl
      · rfl
      · exfalso
        have := hd 0 (by rw [Nat.testBit_zero, h1]; rfl)
        rw [Nat.testBit_zero, h2] at this
        exact absurd this (by decide)
    have hlt : a % 2 ^^^ b % 2 < 2 ^ 1 :=
      Nat.xor_lt_two_pow (by omega) (by omega)
    have e : a + b = 2 ^ 1 * (a / 2 ^^^ b / 2) + (a % 2 ^^^ b % 2) := by
      rw [← ih, ← h0]
      omega
    rw [e]
    apply Nat.eq_of_testBit_eq
    intro q
    have ha' : a.testBit q = if q < 1 then (a % 2).testBit q else (a / 2).testBit (q - 1) := by
      conv_lhs => rw [ea]
      exact Nat.testBit_two_pow_mul_add _ (by omega) q
    have hb' : b.testBit q = if q < 1 then (b % 2).testBit q else (b / 2).testBit (q - 1) := by
      conv_lhs => rw [eb]
      exact Nat.testBit_two_pow_mul_add _ (by omega) q
    rw [Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_xor a b, ha', hb']
    split <;> simp only [Nat.testBit_xor]

theorem sub_land_eq (P m : Nat) : P - (P &&& m) = P ^^^ (P &&& m) := by
  obtain ⟨n, hn⟩ : ∃ n, P < 2 ^ n := ⟨P, Nat.lt_two_pow_self⟩
  have hlt : P ^^^ (P &&& m) < 2 ^ n :=
    Nat.xor_lt_two_pow hn (Nat.lt_of_le_of_lt Nat.and_le_left hn)
  have e := add_eq_xor_of_disj n (P ^^^ (P &&& m)) (P &&& m) hlt
    (Nat.lt_of_le_of_lt Nat.and_le_left hn) (by
      intro q hq
      simp only [Nat.testBit_xor, Nat.testBit_and] at hq ⊢
      cases hP : P.testBit q <;> cases hm : m.testBit q <;> simp_all)
  have e2 : P ^^^ (P &&& m) ^^^ (P &&& m) = P := by
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [e2] at e
  omega

open CFSG.KC.BM.SL in
theorem rowUpd_rows {B : List Nat} (hB : wfMat B = true) (P : Nat) {i t : Nat} (hi : i < 64)
    (ht : t < 64) :
    vrow (rowOf (Nat.lor (mulS B (Nat.land P (Nat.shiftLeft SM i)))
      (Nat.sub P (Nat.land P (Nat.shiftLeft SM i)))) t) =
      if t = i then vrow (rowOf P i) ᵥ* stripMat B else vrow (rowOf P t) := by
  have hPi : ∀ (k : Fin 4370) (t' : Nat), t' < 64 →
      (P &&& (SM <<< i)).testBit (64 * k.val + t') = (decide (t' = i) && P.testBit (64 * k.val + t')) := by
    intro k t' ht'
    rw [Nat.testBit_and, Nat.testBit_shiftLeft, SM_eq, testBit_SMn]
    by_cases e : t' = i
    · subst e
      have e1 : 64 * k.val + t' - t' = 64 * k.val := by omega
      rw [e1]
      have h1 : 64 * k.val < 64 * 4370 := by omega
      have h2 : 64 * k.val % 64 = 0 := by omega
      simp [h1, h2]
    · have : ¬ ((64 * k.val + t' - i) % 64 = 0 ∧ 64 * k.val + t' ≥ i) := by omega
      by_cases h1 : 64 * k.val + t' ≥ i
      · have h2 : ¬ (64 * k.val + t' - i) % 64 = 0 := fun h => this ⟨h, h1⟩
        simp [h1, h2, e]
      · simp [h1, e]
  have hrow : ∀ t' < 64, vrow (rowOf (P &&& (SM <<< i)) t') =
      if t' = i then vrow (rowOf P i) else 0 := by
    intro t' ht'
    funext k
    rw [vrow_rowOf, hPi k t' ht']
    by_cases e : t' = i
    · subst e
      simp [vrow_rowOf]
    · simp [e]
  rw [wfMat_eq] at hB
  funext j
  rw [vrow_rowOf, nlor, nsub, nland, nshl, sub_land_eq, Nat.testBit_or, Nat.testBit_xor]
  have hU := congrFun (mulS_rows (by rw [wfMat_eq]; exact hB) (P &&& (SM <<< i)) ht) j
  rw [hrow t ht, vrow_rowOf] at hU
  by_cases e : t = i
  · subst e
    rw [ite_eq_left rfl] at hU
    rw [ite_eq_left rfl, ← hU, hPi j t ht, decide_eq_true rfl, Bool.true_and]
    cases (mulS B (P &&& SM <<< t)).testBit (64 * j.val + t) <;>
      cases P.testBit (64 * j.val + t) <;> rfl
  · rw [ite_eq_right e, Matrix.zero_vecMul, Pi.zero_apply] at hU
    rw [ite_eq_right e, vrow_rowOf, hPi j t ht, decide_eq_false e, Bool.false_and,
      Bool.xor_false]
    have hU' : (mulS B (P &&& SM <<< i)).testBit (64 * j.val + t) = false := bz_inj hU
    rw [hU', Bool.false_or]

theorem nthN_zero (M : List Nat) : nthN M 0 = M.getD 0 0 := by
  cases M <;> rfl

open CFSG.KC.BM.SL in
theorem e0_vecMul (M : List Nat) (j : Fin 4370) :
    (e0 ᵥ* stripMat M) j = bz ((M.getD 0 0).testBit (64 * j.val)) := by
  unfold e0
  rw [Matrix.single_one_vecMul, Matrix.row_apply, stripMat_eq, stripMatG_apply]
  rfl

open CFSG.KC.BM.SL in
theorem row0_rec : ∀ (Ms : List (List Nat)) (t0 acc : Nat), t0 + Ms.length ≤ 64 →
    ∀ (j : Fin 4370) (t' : Nat), t' < 64 →
      (List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
        (fun M _ ih t acc => forceB (Nat.lor acc (Nat.shiftLeft (Nat.land (nthN M (nat_lit 0)) SM) t))
          (fun a => ih (Nat.succ t) a)) Ms t0 acc : Nat).testBit (64 * j.val + t') =
        (acc.testBit (64 * j.val + t') || (decide (t0 ≤ t' ∧ t' < t0 + Ms.length) &&
          ((Ms.getD (t' - t0) []).getD 0 0).testBit (64 * j.val)))
  | [], t0, acc, _, j, t', _ => by simp
  | M :: Ms, t0, acc, hl, j, t', ht' => by
    change (forceB _ (fun a => List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
        (fun M _ ih t acc => forceB (Nat.lor acc (Nat.shiftLeft (Nat.land (nthN M (nat_lit 0)) SM) t))
          (fun a => ih (Nat.succ t) a)) Ms (Nat.succ t0) a)).testBit _ = _
    rw [forceB_eq', row0_rec Ms (Nat.succ t0) _ (by simp at hl; omega) j t' ht', nlor, nshl, nland,
      Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, SM_eq, testBit_SMn, nthN_zero,
      Bool.or_assoc]
    congr 1
    simp only [List.length_cons]
    by_cases e : t' = t0
    · subst e
      have e1 : 64 * j.val + t' - t' = 64 * j.val := by omega
      have h1 : 64 * j.val < 64 * 4370 := by omega
      have h2 : 64 * j.val % 64 = 0 := by omega
      rw [e1]
      simp [h1, h2]
    · have h1 : ¬ (64 * j.val + t' ≥ t0 ∧ (64 * j.val + t' - t0) % 64 = 0) := by
        simp at hl
        omega
      have e2 : (decide (t0 ≤ t' ∧ t' < t0 + (Ms.length + 1))) =
          decide (Nat.succ t0 ≤ t' ∧ t' < Nat.succ t0 + Ms.length) := by
        congr 1
        apply propext
        omega
      rw [e2]
      by_cases h2 : Nat.succ t0 ≤ t' ∧ t' < Nat.succ t0 + Ms.length
      · have e3 : t' - t0 = (t' - Nat.succ t0) + 1 := by omega
        rw [e3, List.getD_cons_succ]
        by_cases h3 : 64 * j.val + t' ≥ t0
        · have h4 : ¬ (64 * j.val + t' - t0) % 64 = 0 := fun h => h1 ⟨h3, h⟩
          simp [h3, h4]
        · simp [h3]
      · simp only [decide_eq_false h2, Bool.false_and, Bool.or_false]
        by_cases h3 : 64 * j.val + t' ≥ t0
        · have h4 : ¬ (64 * j.val + t' - t0) % 64 = 0 := fun h => h1 ⟨h3, h⟩
          simp [h3, h4]
        · simp [h3]

open CFSG.KC.BM.SL in
theorem row0Strip_rows {Ms : List (List Nat)} (hMs : Ms.length ≤ 64) {t : Nat}
    (ht : t < Ms.length) : vrow (rowOf (row0Strip Ms) t) = e0 ᵥ* stripMat (Ms.getD t []) := by
  funext j
  rw [vrow_rowOf, e0_vecMul]
  unfold row0Strip
  rw [row0_rec Ms 0 0 (by omega) j t (by omega), Nat.zero_testBit, Bool.false_or, Nat.sub_zero,
    decide_eq_true ⟨Nat.zero_le _, by omega⟩, Bool.true_and]

open CFSG.KC.BM.SL in
theorem rep_rows (M : List Nat) {c k t : Nat} (hc : c + 1 = 2 ^ k) (hk : k ≤ 64) (ht : t < k) :
    vrow (rowOf (Nat.mul (Nat.land (nthN M 0) SM) c) t) = e0 ᵥ* stripMat M := by
  funext j
  have hc' : c = 2 ^ k - 1 := by omega
  have hc64 : c < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) hk
    omega
  have hy : ∀ p, (nthN M 0 &&& SM).testBit p = true → p % 64 = 0 := by
    intro p hp
    rw [Nat.testBit_and, Bool.and_eq_true, SM_eq] at hp
    exact SMn_sparse 4370 p hp.2
  rw [vrow_rowOf, e0_vecMul, nmul, nland, Nat.mul_comm, testBit_mul_sparse hc64 j.val _ hy t
    (by omega), hc', Nat.testBit_two_pow_sub_one, decide_eq_true ht, Bool.true_and,
    Nat.testBit_and, SM_eq, testBit_SMn_mul, decide_eq_true j.isLt, Bool.and_true, nthN_zero]

@[expose] noncomputable def commRec (D D' i : Nat) (Cs : List Nat) (j acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun C _ ih j acc => forceB
      ((fun x => Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (nat_lit 18446744073709551616)
            (Nat.add acc (Nat.shiftLeft (nat_lit 1) j)) (Nat.beq x (rowOf D' j)))
          acc (Nat.beq x (rowOf D j)))
        (rowOf C i))
      (fun acc' => forceB (Nat.succ j) (fun j' => ih j' acc'))) Cs j acc

theorem commRec_cons (D D' i C : Nat) (Cs : List Nat) (j acc : Nat) :
    commRec D D' i (C :: Cs) j acc = commRec D D' i Cs (j + 1)
      (if rowOf C i = rowOf D j then acc else if rowOf C i = rowOf D' j then acc + 2 ^ j
        else 2 ^ 64) := by
  change forceB _ (fun acc' => forceB (Nat.succ j) (fun j' => commRec D D' i Cs j' acc')) = _
  rw [CFSG.KC.BM.SL.forceB_eq', CFSG.KC.BM.SL.forceB_eq']
  congr 1
  simp only [CFSG.KC.BM.SL.bool_rec_eq, Nat.beq_eq, CFSG.KC.BM.SL.nadd, CFSG.KC.BM.SL.nshl,
    Nat.one_shiftLeft]
  rfl

theorem commRec_big (D D' i : Nat) : ∀ (Cs : List Nat) (j acc : Nat), 2 ^ 64 ≤ acc →
    2 ^ 64 ≤ commRec D D' i Cs j acc
  | [], _, _, h => h
  | C :: Cs, j, acc, h => by
    rw [commRec_cons]
    apply commRec_big
    split
    · exact h
    · split
      · exact le_trans h (Nat.le_add_right _ _)
      · exact le_rfl

theorem commRec_spec (D D' i : Nat) : ∀ (Cs : List Nat) (j acc : Nat), acc < 2 ^ j →
    commRec D D' i Cs j acc < 2 ^ 64 → ∀ m < Cs.length,
      ((commRec D D' i Cs j acc).testBit (j + m) = true → rowOf (Cs.getD m 0) i = rowOf D' (j + m)) ∧
      ((commRec D D' i Cs j acc).testBit (j + m) = false → rowOf (Cs.getD m 0) i = rowOf D (j + m))
  | [], _, _, _, _, m, hm => absurd hm (by simp)
  | C :: Cs, j, acc, hacc, hr, m, hm => by
    rw [commRec_cons] at hr ⊢
    have hlow : ∀ (Cs : List Nat) (j acc : Nat), acc < 2 ^ j → commRec D D' i Cs j acc < 2 ^ 64 →
        ∀ b < j, (commRec D D' i Cs j acc).testBit b = acc.testBit b := by
      intro Cs
      induction Cs with
      | nil => intro j acc _ _ b _; rfl
      | cons C' Cs ih =>
        intro j acc hacc hr b hb
        rw [commRec_cons] at hr ⊢
        by_cases h1 : rowOf C' i = rowOf D j
        · rw [ite_eq_left h1] at hr ⊢
          exact ih (j + 1) acc (by rw [Nat.pow_succ]; omega) hr b (by omega)
        · rw [ite_eq_right h1] at hr ⊢
          by_cases h2 : rowOf C' i = rowOf D' j
          · rw [ite_eq_left h2] at hr ⊢
            rw [ih (j + 1) _ (by rw [Nat.pow_succ]; omega) hr b (by omega), Nat.add_comm,
              Nat.testBit_two_pow_add_gt hb]
          · rw [ite_eq_right h2] at hr ⊢
            exact absurd (commRec_big D D' i Cs (j + 1) _ le_rfl) (by omega)
    cases m with
    | zero =>
      simp only [Nat.add_zero, List.getD_cons_zero]
      by_cases h1 : rowOf C i = rowOf D j
      · rw [ite_eq_left h1] at hr ⊢
        rw [hlow Cs (j + 1) acc (by rw [Nat.pow_succ]; omega) hr j (by omega),
          Nat.testBit_lt_two_pow hacc]
        exact ⟨fun h => absurd h (by decide), fun _ => h1⟩
      · rw [ite_eq_right h1] at hr ⊢
        by_cases h2 : rowOf C i = rowOf D' j
        · rw [ite_eq_left h2] at hr ⊢
          rw [hlow Cs (j + 1) _ (by rw [Nat.pow_succ]; omega) hr j (by omega), Nat.add_comm,
            Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hacc]
          exact ⟨fun _ => h2, fun h => absurd h (by decide)⟩
        · rw [ite_eq_right h2] at hr ⊢
          exact absurd (commRec_big D D' i Cs (j + 1) _ le_rfl) (by omega)
    | succ m =>
      rw [List.getD_cons_succ]
      have e : j + (m + 1) = (j + 1) + m := by omega
      rw [e]
      have hm' : m < Cs.length := by simp at hm; omega
      by_cases h1 : rowOf C i = rowOf D j
      · rw [ite_eq_left h1] at hr ⊢
        exact commRec_spec D D' i Cs (j + 1) acc (by rw [Nat.pow_succ]; omega) hr m hm'
      · rw [ite_eq_right h1] at hr ⊢
        by_cases h2 : rowOf C i = rowOf D' j
        · rw [ite_eq_left h2] at hr ⊢
          exact commRec_spec D D' i Cs (j + 1) _ (by rw [Nat.pow_succ]; omega) hr m hm'
        · rw [ite_eq_right h2] at hr ⊢
          exact absurd (commRec_big D D' i Cs (j + 1) _ le_rfl) (by omega)

theorem commRow_sound {Cs : List Nat} {D D' i r : Nat} (h : commRow Cs D D' i = r)
    (hr : r < 2 ^ 64) : ∀ j < Cs.length,
      (r.testBit j = true → rowOf (Cs.getD j 0) i = rowOf D' j) ∧
      (r.testBit j = false → rowOf (Cs.getD j 0) i = rowOf D j) := by
  intro j hj
  have e : commRow Cs D D' i = commRec D D' i Cs 0 0 := rfl
  rw [e] at h
  subst h
  have := commRec_spec D D' i Cs 0 0 (by norm_num) hr j hj
  rwa [Nat.zero_add] at this

@[expose] noncomputable def vmR (k M v acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih M v acc => forceB
      (Nat.xor acc (Nat.mul (Nat.land v (nat_lit 1)) (Nat.land M (nat_lit 4294967295))))
      (fun acc' => ih (Nat.shiftRight M (nat_lit 32)) (Nat.shiftRight v (nat_lit 1)) acc'))
    k M v acc

theorem vmR_succ (k M v acc : Nat) :
    vmR (k + 1) M v acc = vmR k (M >>> 32) (v >>> 1) (acc ^^^ (v &&& 1) * (M &&& (2 ^ 32 - 1))) := by
  change forceB _ (fun acc' => vmR k (Nat.shiftRight M 32) (Nat.shiftRight v 1) acc') = _
  rw [CFSG.KC.BM.SL.forceB_eq']
  rfl

theorem vmR_lt : ∀ (k M v acc : Nat), acc < 2 ^ 32 → vmR k M v acc < 2 ^ 32
  | 0, _, _, _, h => h
  | k + 1, M, v, acc, h => by
    rw [vmR_succ]
    apply vmR_lt
    apply Nat.xor_lt_two_pow h
    rw [Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one v with h' | h' <;> rw [h']
    · simp
    · rw [Nat.one_mul]
      exact CFSG.KC.Benes.land_ones_lt M 32

open CFSG.KC.BM.SL in
theorem vmR_bit {j : Nat} (hj : j < 32) : ∀ (k M v acc : Nat),
    bz ((vmR k M v acc).testBit j) = bz (acc.testBit j) +
      ∑ l ∈ Finset.range k, bz (v.testBit l) * bz ((M >>> (32 * l)).testBit j)
  | 0, _, _, _ => by simp [vmR]
  | k + 1, M, v, acc => by
    rw [vmR_succ, vmR_bit hj k, Nat.testBit_xor, bz_xor, testBit_and_one_mul, bz_and,
      Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hj, Bool.and_true,
      Finset.sum_range_succ']
    simp only [Nat.testBit_shiftRight, Nat.mul_zero, Nat.zero_add]
    have e : ∀ l, 32 + (32 * l + j) = 32 * (l + 1) + j := fun l => by ring
    have e2 : ∀ l, 1 + l = l + 1 := fun l => Nat.add_comm 1 l
    simp only [e, e2]
    ring

theorem vm32_eq (k M v : Nat) : vm32 k M v = vmR k M v 0 := rfl

theorem vm32_lt (k M v : Nat) : vm32 k M v < 2 ^ 32 := by
  rw [vm32_eq]
  exact vmR_lt k M v 0 (by norm_num)

theorem vm32_bit (k M v : Nat) {j : Nat} (hj : j < 32) :
    (if (vm32 k M v).testBit j then (1 : ZMod 2) else 0) =
      ∑ l ∈ Finset.range k, (if v.testBit l then 1 else 0) *
        (if (Nat.shiftRight M (32 * l)).testBit j then 1 else 0) := by
  have := vmR_bit hj k M v 0
  rw [Nat.zero_testBit, CFSG.KC.BM.SL.bz_false, zero_add] at this
  exact this

open CFSG.KC.BM.SL in
theorem vecMul_strip {R : List (List Nat)} {S : List Nat} (h : AllBlocks R S 0)
    (hS : wfMat S = true) {v : Nat} (_hv : v < 2 ^ 4370) :
    vecMul R v < 2 ^ 4370 ∧ vecN (vecMul R v) = vecN v ᵥ* stripMat S := by
  rw [wfMat_eq] at hS
  obtain ⟨hl, hb⟩ := allBlocks_spec h
  have hS69 := (wf_bit hS).1
  have hR : ∀ s < 69, (R.getD s []).length = rowsSn 4370 s ∧
      sob 279680 4370 (R.getD s []) 0 0 = S.getD s 0 := fun s hs => by
    have := blockOK_spec (hb s (by omega))
    rwa [Nat.zero_add] at this
  have hrow := fun {i : Nat} (hi : i < 4370) =>
    rows_of_blocks (by norm_num) (by norm_num) hS hR hi
  have hfl := flatten_getD R (fun s hs => by rw [(hR s (by omega)).1, rowsSn_eq]; omega)
    (fun s hs => by rw [(hR s (by omega)).1, rowsSn_eq]; omega)
  have hz : ∀ m, 4370 ≤ m → R.flatten.getD m 0 = 0 := by
    intro m hm
    rw [hfl]
    by_cases hs : m / 64 < 69
    · apply List.getD_eq_default
      rw [(hR _ hs).1, rowsSn_eq]
      omega
    · rw [List.getD_eq_default R [] (by omega : R.length ≤ m / 64)]
      simp
  have hmem : ∀ r ∈ R.flatten, r < 2 ^ 4370 := by
    intro r hr
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hr
    have e := List.getD_eq_getElem (l := R.flatten) (d := 0) hm
    by_cases hm' : m < 4370
    · rw [← e, hfl]
      exact (hrow hm').1
    · rw [← e, hz m (by omega)]
      exact Nat.two_pow_pos _
  rw [vecMul_eq_vOuter, vOuter_eq]
  refine ⟨VL_lt _ hmem v 0 (Nat.two_pow_pos _), ?_⟩
  funext j
  change bz ((VL R.flatten v 0).testBit j.val) = ∑ i : Fin 4370, bz (v.testBit i.val) *
    stripMat S i j
  have e3 : ∑ i : Fin 4370, bz (v.testBit i.val) * stripMat S i j =
      ∑ i : Fin 4370, bz (v.testBit i.val) * bz ((R.flatten.getD i.val 0).testBit j.val) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [stripMat_eq, stripMatG_apply, hfl, (hrow i.isLt).2]
  rw [VL_bit, Nat.zero_testBit, bz_false, zero_add, e3,
    Fin.sum_univ_eq_sum_range (fun i => bz (v.testBit i) *
      bz ((R.flatten.getD i 0).testBit j.val)) 4370]
  have e1 : ∑ m ∈ Finset.range R.flatten.length, bz (v.testBit m) *
      bz ((R.flatten.getD m 0).testBit j.val) = ∑ m ∈ Finset.range (R.flatten.length + 4370),
        bz (v.testBit m) * bz ((R.flatten.getD m 0).testBit j.val) := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    rw [Finset.mem_range, Nat.not_lt] at hm
    rw [List.getD_eq_default _ _ hm, Nat.zero_testBit, bz_false, mul_zero]
  have e2 : ∑ m ∈ Finset.range 4370, bz (v.testBit m) * bz ((R.flatten.getD m 0).testBit j.val) =
      ∑ m ∈ Finset.range (R.flatten.length + 4370),
        bz (v.testBit m) * bz ((R.flatten.getD m 0).testBit j.val) := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    rw [Finset.mem_range, Nat.not_lt] at hm
    rw [hz m hm, Nat.zero_testBit, bz_false, mul_zero]
  rw [e1, e2]

open CFSG.KC.BM.SL in
theorem eqMat_self : ∀ X : List Nat, eqMat X X = true
  | [] => rfl
  | x :: X => by
    change Bool.rec (motive := fun _ => Bool) false (eqMat X X) (Nat.beq x x) = true
    rw [Nat.beq_refl]
    exact eqMat_self X

open CFSG.KC.BM.SL in
theorem eqMat_sound {X Y : List Nat} (hX : wfMat X = true) (hY : wfMat Y = true)
    (h : notB (eqMat X Y) = true) : stripMat X ≠ stripMat Y := by
  intro e
  rw [wfMat_eq] at hX hY
  rw [stripMatG_inj (stripShape_of_wf hX) (stripShape_of_wf hY) e, eqMat_self] at h
  exact absurd h (by decide)

theorem vecN_injective {v w : Nat} (hv : v < 2 ^ 4370) (hw : w < 2 ^ 4370) (h : vecN v = vecN w) :
    v = w := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 4370
  · have e := congrFun h ⟨j, hj⟩
    simp only [vecN] at e
    by_cases a : v.testBit j <;> by_cases b : w.testBit j <;> simp_all
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

end CFSG.KC.BM

end
