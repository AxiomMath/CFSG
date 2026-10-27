module

public import CFSG.Certificates.Kernel.H9Four.Codes
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.H9Four.Masks

open CFSG.Quasithin.H13.H9Four CFSG.KC.H9Four CFSG.KC.H9Four.Codes CFSG.KC.Ord CFSG.KC.LQT.P
  CFSG.KC.Misc CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec

@[expose] def ind (p : Bool) : ZMod 2 := if p then 1 else 0

theorem ind_and (p q : Bool) : ind (p && q) = ind p * ind q := by cases p <;> cases q <;> decide

theorem ind_xor (p q : Bool) : ind (p ^^ q) = ind p + ind q := by cases p <;> cases q <;> decide

theorem ind_inj {p q : Bool} : ind p = ind q ↔ p = q := by cases p <;> cases q <;> decide

theorem bit_eq (v n : ℕ) : bit v n = if v.testBit n then 1 else 0 := by
  rw [bit, land_eq, shiftRight_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ n) with h | h <;> simp [h]

theorem testBit_bit (v n m : ℕ) : (bit v n).testBit m = (decide (m = 0) && v.testBit n) := by
  rw [bit_eq]
  cases v.testBit n
  · simp
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp only [if_true]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt (Nat.one_lt_two_pow hm.ne')]
      simp [hm.ne']

theorem testBit_mulBit (v n P m : ℕ) : (Nat.mul (bit v n) P).testBit m = (v.testBit n && P.testBit m) := by
  rw [bit_eq]
  cases v.testBit n <;> simp

theorem fullM_eq : fullM = 2 ^ 256 - 1 := by
  rw [fullM, shl1_eq]
  rfl

theorem testBit_fullM (w : ℕ) : fullM.testBit w = decide (w < 256) := by
  rw [fullM_eq, Nat.testBit_two_pow_sub_one]

theorem testBit_plane_lt : ∀ s < 8, ∀ w < 256, (plane s).testBit w = w.testBit s := by
  decide +kernel

theorem plane_lt : ∀ s < 8, plane s < 2 ^ 256 := by decide +kernel

theorem testBit_plane {s : ℕ} (hs : s < 8) (w : ℕ) :
    (plane s).testBit w = (decide (w < 256) && w.testBit s) := by
  by_cases hw : w < 256
  · simp [hw, testBit_plane_lt s hs w hw]
  · simp only [hw, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le (plane_lt s hs) (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem testBit_lt_256 {m : ℕ} (hm : m < 256) {n : ℕ} (hn : 8 ≤ n) : m.testBit n = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn))

theorem eq_of_testBit_lt_256 {m w : ℕ} (hm : m < 256) (hw : w < 256)
    (h : ∀ n < 8, m.testBit n = w.testBit n) : m = w := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 8
  · exact h n hn
  · rw [testBit_lt_256 hm (by omega), testBit_lt_256 hw (by omega)]

theorem lt_256_of_testBit {m : ℕ} (h : ∀ n, 8 ≤ n → m.testBit n = false) : m < 256 := by
  have := Nat.lt_pow_two_of_testBit m (n := 8) (fun i hi => h i hi)
  simpa using this

theorem ptOfCode_fst (w : ℕ) :
    (ptOfCode w).1 = Multiplicative.ofAdd fun i => ind (w.testBit i.val) := rfl

theorem ptOfCode_snd (w : ℕ) :
    (ptOfCode w).2 = Multiplicative.ofAdd fun i => ind (w.testBit (4 + i.val)) := rfl

theorem ptOfCode_eq_iff {m w : ℕ} (hm : m < 256) (hw : w < 256) :
    ptOfCode m = ptOfCode w ↔ m = w := by
  refine ⟨fun h => eq_of_testBit_lt_256 hm hw fun n hn => ?_, fun h => h ▸ rfl⟩
  have h1 := congrArg (fun p : Pt => Multiplicative.toAdd p.1) h
  have h2 := congrArg (fun p : Pt => Multiplicative.toAdd p.2) h
  simp only [ptOfCode_fst, ptOfCode_snd, toAdd_ofAdd] at h1 h2
  by_cases hn4 : n < 4
  · exact ind_inj.mp (congrFun h1 ⟨n, hn4⟩)
  · have := ind_inj.mp (congrFun h2 ⟨n - 4, by omega⟩)
    simpa [show 4 + (n - 4) = n by omega] using this

theorem ptOfCode_xor (a b : ℕ) : ptOfCode (a ^^^ b) = ptOfCode a * ptOfCode b := by
  refine Prod.ext ?_ ?_
  · change Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add]
    congr 1
    funext i
    simp only [Pi.add_apply, Nat.testBit_xor]
    generalize a.testBit _ = p
    generalize b.testBit _ = q
    cases p <;> cases q <;> rfl
  · change Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add]
    congr 1
    funext i
    simp only [Pi.add_apply, Nat.testBit_xor]
    generalize a.testBit _ = p
    generalize b.testBit _ = q
    cases p <;> cases q <;> rfl

theorem ptOfCode_zero : ptOfCode 0 = 1 := by
  refine Prod.ext ?_ ?_ <;>
  · change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    funext i
    simp [ind]

theorem mul_self_pt (p : Pt) : p * p = 1 := by
  have h : ∀ c : ZMod 2, c + c = 0 := by decide
  refine Prod.ext ?_ ?_
  · change Multiplicative.ofAdd (Multiplicative.toAdd p.1 + Multiplicative.toAdd p.1) =
      Multiplicative.ofAdd 0
    congr 1
    funext i
    exact h _
  · change Multiplicative.ofAdd (Multiplicative.toAdd p.2 + Multiplicative.toAdd p.2) =
      Multiplicative.ofAdd 0
    congr 1
    funext i
    exact h _

theorem inv_pt (p : Pt) : p⁻¹ = p := by
  rw [inv_eq_iff_mul_eq_one, mul_self_pt]

theorem allPts_nodup : allPts.Nodup := by
  unfold allPts
  refine (List.nodup_range).map_on fun a ha b hb h => ?_
  exact (ptOfCode_eq_iff (List.mem_range.mp ha) (List.mem_range.mp hb)).mp h

theorem card_pt : Fintype.card Pt = 256 := by
  change Fintype.card (Multiplicative (Fin 4 → ZMod 2) × Multiplicative (Fin 4 → ZMod 2)) = 256
  simp [Fintype.card_prod, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card]

theorem mem_allPts (p : Pt) : p ∈ allPts := by
  have h1 : allPts.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup allPts_nodup, card_pt]
    simp [allPts]
  rw [← List.mem_toFinset, h1]
  exact Finset.mem_univ p

theorem exists_code_pt (p : Pt) : ∃ w < 256, ptOfCode w = p := by
  obtain ⟨w, hw, h⟩ := List.mem_map.mp (mem_allPts p)
  exact ⟨w, List.mem_range.mp hw, h⟩

theorem app_coord (k : ℕ) (f : Fin 4 → ZMod 2) (r : Fin 4) :
    Multiplicative.toAdd ((Mat.ofCode k).app (Multiplicative.ofAdd f)) r =
      ∑ s : Fin 4, ind (k.testBit (4 * r.val + s.val)) * f s := by
  simp only [Mat.app, toAdd_ofAdd, toMatrix_ofCode, Matrix.mulVec, dotProduct, pkMat,
    Matrix.of_apply, ind]

theorem tr_app_coord (k : ℕ) (f : Fin 4 → ZMod 2) (r : Fin 4) :
    Multiplicative.toAdd ((Mat.tr (Mat.ofCode k)).app (Multiplicative.ofAdd f)) r =
      ∑ s : Fin 4, ind (k.testBit (4 * s.val + r.val)) * f s := by
  rw [← ofCode_tr4, app_coord]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [testBit_tr4 k r.isLt s.isLt]

theorem ind_mul4 (a b : ℕ) (i j : Fin 4) :
    ind ((mul4 a b).testBit (4 * i.val + j.val)) =
      ∑ s : Fin 4, ind (a.testBit (4 * i.val + s.val)) * ind (b.testBit (4 * s.val + j.val)) := by
  have h := congrFun (congrFun (pkMat_mul4 a b) i) j
  simp only [Matrix.mul_apply, pkMat, Matrix.of_apply] at h
  exact h

theorem testBit_land15 (v n : ℕ) : (v &&& 15).testBit n = (decide (n < 4) && v.testBit n) := by
  rw [show (15 : ℕ) = 2 ^ 4 - 1 by norm_num, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Bool.and_comm]

theorem testBit_colV (x : ℕ) (s : Fin 4) : (colV x).testBit (4 * s.val) = x.testBit s.val := by
  simp only [colV, lor_eq, shiftLeft_eq, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_bit]
  fin_cases s <;> simp

theorem testBit_gather (z n : ℕ) : (gather z).testBit n = (decide (n < 4) && z.testBit (4 * n)) := by
  simp only [gather, lor_eq, shiftLeft_eq, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_bit]
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp
  | n + 4 => simp

theorem actK_bits (t w : ℕ) (r : Fin 4) :
    ind ((actK t w).testBit r.val) =
      Multiplicative.toAdd ((decE t).act (ptOfCode w)).1 r ∧
    ind ((actK t w).testBit (4 + r.val)) =
      Multiplicative.toAdd ((decE t).act (ptOfCode w)).2 r := by
  unfold actK
  simp only [letN_eq]
  cases hb : Nat.beq (fb t) 1
  · simp only [Elt.act, decE, hb, Bool.false_eq_true, ↓reduceIte, ptOfCode_fst, ptOfCode_snd,
      app_coord, tr_app_coord]
    simp only [lor_eq, shiftLeft_eq, shiftRight_eq, Nat.testBit_or, Nat.testBit_shiftLeft,
      land_eq, testBit_land15, testBit_gather]
    refine ⟨?_, ?_⟩
    · have h1 := ind_mul4 (fa t) (colV (w &&& 15)) r 0
      simp only [r.isLt, decide_true, Bool.true_and, show ¬ 4 ≤ r.val by omega, decide_false,
        Bool.false_and, Bool.or_false]
      simp only [Fin.val_zero, Nat.add_zero] at h1
      rw [h1]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [testBit_colV, testBit_land15]
      simp [s.isLt]
    · have h1 := ind_mul4 ((w >>> 4) &&& 15) (fai t) 0 r
      simp only [show ¬ 4 + r.val < 4 by omega, decide_false, Bool.false_and, Bool.false_or,
        show 4 ≤ 4 + r.val by omega, decide_true, Bool.true_and, show 4 + r.val - 4 = r.val by omega,
        r.isLt]
      simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add] at h1
      rw [h1]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [testBit_land15, Nat.testBit_shiftRight, mul_comm]
      simp [s.isLt, Nat.add_comm 4]
  · simp only [Elt.act, decE, hb, ↓reduceIte, ptOfCode_fst, ptOfCode_snd, app_coord, tr_app_coord]
    simp only [lor_eq, shiftLeft_eq, shiftRight_eq, Nat.testBit_or, Nat.testBit_shiftLeft,
      land_eq, testBit_land15, testBit_gather]
    refine ⟨?_, ?_⟩
    · have h1 := ind_mul4 (fa t) (colV ((w >>> 4) &&& 15)) r 0
      simp only [r.isLt, decide_true, Bool.true_and, show ¬ 4 ≤ r.val by omega, decide_false,
        Bool.false_and, Bool.or_false]
      simp only [Fin.val_zero, Nat.add_zero] at h1
      rw [h1]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [testBit_colV, testBit_land15, Nat.testBit_shiftRight]
      simp [s.isLt, Nat.add_comm 4]
    · have h1 := ind_mul4 (w &&& 15) (fai t) 0 r
      simp only [show ¬ 4 + r.val < 4 by omega, decide_false, Bool.false_and, Bool.false_or,
        show 4 ≤ 4 + r.val by omega, decide_true, Bool.true_and, show 4 + r.val - 4 = r.val by omega,
        r.isLt]
      simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add] at h1
      rw [h1]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [testBit_land15, mul_comm]
      simp [s.isLt]

theorem actK_high (t w : ℕ) {n : ℕ} (hn : 8 ≤ n) : (actK t w).testBit n = false := by
  unfold actK
  simp only [letN_eq]
  cases Nat.beq (fb t) 1 <;>
  · simp only [lor_eq, shiftLeft_eq, Nat.testBit_or, Nat.testBit_shiftLeft, land_eq,
      testBit_land15, testBit_gather]
    simp [show ¬ n < 4 by omega, show ¬ n - 4 < 4 by omega]

theorem actK_lt (t w : ℕ) : actK t w < 256 := lt_256_of_testBit fun _ hn => actK_high t w hn

theorem ptOfCode_actK (t w : ℕ) : ptOfCode (actK t w) = (decE t).act (ptOfCode w) := by
  refine Prod.ext ?_ ?_
  · rw [ptOfCode_fst]
    apply Multiplicative.toAdd.injective
    funext r
    rw [toAdd_ofAdd]
    exact (actK_bits t w r).1
  · rw [ptOfCode_snd]
    apply Multiplicative.toAdd.injective
    funext r
    rw [toAdd_ofAdd]
    exact (actK_bits t w r).2

theorem fixed_iff_actK (t : ℕ) {w : ℕ} (hw : w < 256) :
    (decE t).act (ptOfCode w) = ptOfCode w ↔ actK t w = w := by
  rw [← ptOfCode_actK, ptOfCode_eq_iff (actK_lt t w) hw]

theorem ind_actK1 (t w : ℕ) (r : Fin 4) : ind ((actK t w).testBit r.val) =
    ∑ s : Fin 4, ind ((fa t).testBit (4 * r.val + s.val)) * ind (w.testBit (s.val + 4 * fb t)) := by
  rw [(actK_bits t w r).1]
  rcases lt_two (fb_lt t) with h | h
  · simp [Elt.act, decE, h, ptOfCode_fst, app_coord]
  · simp [Elt.act, decE, h, ptOfCode_snd, app_coord, Nat.add_comm]

theorem ind_actK2 (t w : ℕ) (r : Fin 4) : ind ((actK t w).testBit (4 + r.val)) =
    ∑ s : Fin 4, ind ((fai t).testBit (4 * s.val + r.val)) *
      ind (w.testBit (s.val + (4 - 4 * fb t))) := by
  rw [(actK_bits t w r).2]
  rcases lt_two (fb_lt t) with h | h
  · simp [Elt.act, decE, h, ptOfCode_snd, tr_app_coord, Nat.add_comm]
  · simp [Elt.act, decE, h, ptOfCode_fst, tr_app_coord]

theorem testBit_recXor4 (f : ℕ → ℕ) (w : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun s acc => Nat.xor acc (f s)) (nat_lit 4)).testBit w =
      ((((f 0).testBit w ^^ (f 1).testBit w) ^^ (f 2).testBit w) ^^ (f 3).testBit w) := by
  change (Nat.xor (Nat.xor (Nat.xor (Nat.xor 0 (f 0)) (f 1)) (f 2)) (f 3)).testBit w = _
  simp only [xor_eq, Nat.testBit_xor, Nat.zero_testBit, Bool.false_xor]

theorem testBit_xorFull (X : ℕ) {w : ℕ} (hw : w < 256) :
    (Nat.xor fullM X).testBit w = !X.testBit w := by
  rw [xor_eq, Nat.testBit_xor, testBit_fullM, decide_eq_true hw, Bool.true_xor]

theorem testBit_lor4 (F0 F1 F2 F3 w : ℕ) :
    (Nat.lor (Nat.lor (Nat.lor (Nat.lor (nat_lit 0) F0) F1) F2) F3).testBit w =
      (((F0.testBit w || F1.testBit w) || F2.testBit w) || F3.testBit w) := by
  simp only [lor_eq, Nat.testBit_or]
  rw [Nat.zero_testBit, Bool.false_or]

theorem ind_rowP (row off w : ℕ) (hoff : off ≤ 4) (hw : w < 256) :
    ind ((rowP row off).testBit w) =
      ∑ s : Fin 4, ind (row.testBit s.val) * ind (w.testBit (s.val + off)) := by
  have hp : ∀ s < 4, (plane (Nat.add s off)).testBit w = w.testBit (s + off) := fun s hs =>
    testBit_plane_lt _ (by change s + off < 8; omega) w hw
  have h := testBit_recXor4 (fun s => Nat.mul (bit row s) (plane (Nat.add s off))) w
  simp only at h
  unfold rowP
  rw [h]
  simp only [testBit_mulBit, hp 0 (by norm_num), hp 1 (by norm_num), hp 2 (by norm_num),
    hp 3 (by norm_num), ind_xor, ind_and, Fin.sum_univ_four]
  simp

theorem testBit_row (a r s : ℕ) (hs : s < 4) :
    (Nat.land (Nat.shiftRight a (Nat.mul (nat_lit 4) r)) (nat_lit 15)).testBit s =
      a.testBit (4 * r + s) := by
  rw [land_eq, shiftRight_eq, testBit_land15, Nat.testBit_shiftRight]
  simp [hs, Nat.mul_eq]

theorem testBit_colOf (c i s : ℕ) (hs : s < 4) : (colOf c i).testBit s = c.testBit (4 * s + i) := by
  simp only [colOf, lor_eq, shiftLeft_eq, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_bit,
    Nat.add_eq]
  interval_cases s <;> simp [Nat.add_comm]

theorem fix_term (t w r : ℕ) (hr : r < 4) (hw : w < 256) :
    (Nat.lor (Nat.xor (plane r) (rowP (Nat.land (Nat.shiftRight (fa t) (Nat.mul (nat_lit 4) r))
      (nat_lit 15)) (Nat.mul (nat_lit 4) (fb t))))
      (Nat.xor (plane (Nat.add r (nat_lit 4))) (rowP (colOf (fai t) r)
        (Nat.sub (nat_lit 4) (Nat.mul (nat_lit 4) (fb t)))))).testBit w =
    (((actK t w).testBit r ^^ w.testBit r) || ((actK t w).testBit (4 + r) ^^ w.testBit (4 + r))) := by
  have hb := fb_lt t
  simp only [lor_eq, xor_eq, Nat.testBit_or, Nat.testBit_xor]
  congr 1
  · rw [← ind_inj, ind_xor, ind_xor, testBit_plane_lt r (by omega) w hw,
      ind_rowP _ _ w (by change 4 * fb t ≤ 4; omega) hw, ind_actK1 t w ⟨r, hr⟩, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [testBit_row _ _ _ s.isLt]
    rfl
  · rw [← ind_inj, ind_xor, ind_xor, testBit_plane_lt _ (by change r + 4 < 8; omega) w hw,
      ind_rowP _ _ w (by change 4 - 4 * fb t ≤ 4; omega) hw, ind_actK2 t w ⟨r, hr⟩, add_comm,
      show Nat.add r 4 = 4 + r by change r + 4 = 4 + r; omega]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [testBit_colOf _ _ _ s.isLt]
    rfl

theorem testBit_fixK_actK (t : ℕ) {w : ℕ} (hw : w < 256) :
    (fixK t).testBit w = decide (actK t w = w) := by
  unfold fixK
  simp only [letN_eq]
  rw [testBit_xorFull _ hw, testBit_lor4, fix_term t w _ ?_ hw, fix_term t w _ ?_ hw,
    fix_term t w _ ?_ hw, fix_term t w _ ?_ hw]
  rotate_left
  · decide
  · decide
  · decide
  · decide
  have hx : ∀ a b : Bool, (a ^^ b) = false ↔ a = b := by decide
  have hT : ∀ x : Bool, (true ^^ x) = true ↔ x = false := by decide
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.not_eq_true']
  simp only [Bool.or_eq_false_iff, hx]
  constructor
  · intro h
    apply eq_of_testBit_lt_256 (actK_lt t w) hw
    intro n hn
    interval_cases n <;> simp_all
  · intro h
    simp [h]

theorem testBit_rowP_high (row off : ℕ) (hoff : off ≤ 4) {n : ℕ} (hn : 256 ≤ n) :
    (rowP row off).testBit n = false := by
  have hp : ∀ s < 4, (plane (Nat.add s off)).testBit n = false := fun s hs => by
    rw [testBit_plane (by change s + off < 8; omega)]
    simp [show ¬ n < 256 by omega]
  have h := testBit_recXor4 (fun s => Nat.mul (bit row s) (plane (Nat.add s off))) n
  simp only at h
  unfold rowP
  rw [h]
  simp only [testBit_mulBit, hp 0 (by norm_num), hp 1 (by norm_num), hp 2 (by norm_num),
    hp 3 (by norm_num), Bool.and_false, Bool.xor_false]

theorem fix_term_high (t r : ℕ) (hr : r < 4) {n : ℕ} (hn : 256 ≤ n) :
    (Nat.lor (Nat.xor (plane r) (rowP (Nat.land (Nat.shiftRight (fa t) (Nat.mul (nat_lit 4) r))
      (nat_lit 15)) (Nat.mul (nat_lit 4) (fb t))))
      (Nat.xor (plane (Nat.add r (nat_lit 4))) (rowP (colOf (fai t) r)
        (Nat.sub (nat_lit 4) (Nat.mul (nat_lit 4) (fb t)))))).testBit n = false := by
  have hb := fb_lt t
  simp only [lor_eq, xor_eq, Nat.testBit_or, Nat.testBit_xor]
  rw [testBit_plane (by omega), testBit_plane (by change r + 4 < 8; omega),
    testBit_rowP_high _ _ (by change 4 * fb t ≤ 4; omega) hn,
    testBit_rowP_high _ _ (by change 4 - 4 * fb t ≤ 4; omega) hn]
  simp [show ¬ n < 256 by omega]

theorem testBit_fixK_high (t : ℕ) {n : ℕ} (hn : 256 ≤ n) : (fixK t).testBit n = false := by
  unfold fixK
  simp only [letN_eq]
  rw [xor_eq, Nat.testBit_xor, testBit_fullM, decide_eq_false (by omega), Bool.false_xor,
    testBit_lor4, fix_term_high t _ ?_ hn, fix_term_high t _ ?_ hn, fix_term_high t _ ?_ hn,
    fix_term_high t _ ?_ hn]
  · rfl
  all_goals decide

theorem testBit_fixK (t : ℕ) {w : ℕ} (hw : w < 256) :
    (fixK t).testBit w = decide ((decE t).act (ptOfCode w) = ptOfCode w) := by
  rw [testBit_fixK_actK t hw]
  simp only [fixed_iff_actK t hw]

theorem testBit_fixAllK (G : List ℕ) {u : ℕ} (hu : u < 256) :
    (fixAllK G).testBit u = G.all fun g => (fixK g).testBit u := by
  induction G with
  | nil =>
    change fullM.testBit u = true
    rw [testBit_fullM, decide_eq_true hu]
  | cons g G ih =>
    change (Nat.land (fixK g) (fixAllK G)).testBit u = _
    rw [land_eq, Nat.testBit_and, ih, List.all_cons]

theorem recCount (m : ℕ) (g : ℕ → ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun w acc => Nat.add acc (bit m (g w))) n =
      ((List.range n).filter fun w => m.testBit (g w)).length
  | 0 => rfl
  | n + 1 => by
    change Nat.add (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun w acc => Nat.add acc (bit m (g w))) n) (bit m (g n)) = _
    rw [recCount m g n, List.range_succ, List.filter_append, List.length_append, bit_eq]
    cases hc : m.testBit (g n) <;> simp [hc]

theorem pop256_eq (m : ℕ) : pop256 m = ((List.range 256).filter fun w => m.testBit w).length :=
  recCount m (fun w => w) 256

theorem pop1_eq (m : ℕ) : pop1 m = ((List.range 16).filter fun w => m.testBit w).length :=
  recCount m (fun w => w) 16

theorem pop2_eq (m : ℕ) : pop2 m = ((List.range 16).filter fun y => m.testBit (16 * y)).length :=
  recCount m (fun y => Nat.mul 16 y) 16

theorem len_filter_allPts (P : Pt → Bool) (p : ℕ → Bool) (h : ∀ w < 256, P (ptOfCode w) = p w) :
    (allPts.filter P).length = ((List.range 256).filter p).length := by
  unfold allPts
  rw [List.filter_map, List.length_map]
  congr 1
  exact List.filter_congr fun w hw => h w (List.mem_range.mp hw)

theorem range256_lt16 : (List.range 256).filter (fun w => decide (w < 16)) = List.range 16 := by
  decide +kernel

theorem range256_mod16 :
    (List.range 256).filter (fun w => decide (w % 16 = 0)) = (List.range 16).map (16 * ·) := by
  decide +kernel

theorem count_lt16 (m : ℕ) :
    ((List.range 256).filter fun w => m.testBit w && decide (w < 16)).length = pop1 m := by
  rw [pop1_eq, ← range256_lt16, List.filter_filter]

theorem count_mod16 (m : ℕ) :
    ((List.range 256).filter fun w => m.testBit w && decide (w % 16 = 0)).length = pop2 m := by
  rw [pop2_eq, ← List.filter_filter, range256_mod16, List.filter_map, List.length_map]
  rfl

theorem low_bits : ∀ u < 256, (u.testBit 4 = false ∧ u.testBit 5 = false ∧ u.testBit 6 = false ∧
    u.testBit 7 = false) ↔ u < 16 := by decide +kernel

theorem high_bits : ∀ u < 256, (u.testBit 0 = false ∧ u.testBit 1 = false ∧ u.testBit 2 = false ∧
    u.testBit 3 = false) ↔ u % 16 = 0 := by decide +kernel

theorem ofAdd_eq_one_iff (f : Fin 4 → ZMod 2) :
    Multiplicative.ofAdd f = 1 ↔ f 0 = 0 ∧ f 1 = 0 ∧ f 2 = 0 ∧ f 3 = 0 := by
  rw [← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    fin_cases i <;> assumption

theorem ind_eq_zero (p : Bool) : ind p = 0 ↔ p = false := by cases p <;> decide

theorem ptOfCode_snd_eq_one {u : ℕ} (hu : u < 256) :
    ((ptOfCode u).2 == 1) = decide (u < 16) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← low_bits u hu, ptOfCode_snd,
    ofAdd_eq_one_iff]
  simp only [ind_eq_zero]
  rfl

theorem ptOfCode_fst_eq_one {u : ℕ} (hu : u < 256) :
    ((ptOfCode u).1 == 1) = decide (u % 16 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← high_bits u hu, ptOfCode_fst,
    ofAdd_eq_one_iff]
  simp only [ind_eq_zero]
  rfl

theorem mem_closure_insert (s : Pt) (A : Set Pt) (x : Pt) :
    x ∈ Subgroup.closure (insert s A) ↔
      x ∈ Subgroup.closure A ∨ x * s ∈ Subgroup.closure A := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact Or.inr (by rw [mul_self_pt]; exact Subgroup.one_mem _)
      · exact Or.inl (Subgroup.subset_closure hy)
    | one => exact Or.inl (Subgroup.one_mem _)
    | mul y z _ _ hy hz =>
      rcases hy with hy | hy <;> rcases hz with hz | hz
      · exact Or.inl (Subgroup.mul_mem _ hy hz)
      · exact Or.inr (by rw [mul_assoc]; exact Subgroup.mul_mem _ hy hz)
      · exact Or.inr (by rw [mul_right_comm]; exact Subgroup.mul_mem _ hy hz)
      · refine Or.inl ?_
        have := Subgroup.mul_mem _ hy hz
        rwa [mul_mul_mul_comm, mul_self_pt, mul_one] at this
    | inv y _ hy => rwa [inv_pt]
  · rintro (hx | hx)
    · exact Subgroup.closure_mono (Set.subset_insert _ _) hx
    · have h1 := Subgroup.closure_mono (Set.subset_insert s A) hx
      have h2 : s ∈ Subgroup.closure (insert s A) := Subgroup.subset_closure (Set.mem_insert _ _)
      have := Subgroup.mul_mem _ h1 h2
      rwa [mul_assoc, mul_self_pt, mul_one] at this

theorem mem_spanList : ∀ (L : List Pt) (x : Pt),
    x ∈ spanList L ↔ x ∈ Subgroup.closure {y | y ∈ L}
  | [], x => by
    simp only [spanList, List.mem_singleton, List.not_mem_nil, Set.setOf_false,
      Subgroup.closure_empty, Subgroup.mem_bot]
  | s :: ss, x => by
    have e : {y | y ∈ s :: ss} = insert s {y | y ∈ ss} := by
      ext y
      simp
    rw [e, mem_closure_insert]
    simp only [spanList]
    split_ifs with h
    · rw [mem_spanList ss x]
      rw [List.contains_iff_mem, mem_spanList ss s] at h
      refine ⟨Or.inl, fun h1 => h1.elim id fun h2 => ?_⟩
      have := Subgroup.mul_mem _ h2 h
      rwa [mul_assoc, mul_self_pt, mul_one] at this
    · rw [List.mem_append, mem_spanList ss x, List.mem_map]
      refine or_congr Iff.rfl ⟨fun ⟨y, hy, hxy⟩ => ?_, fun h1 => ⟨x * s, ?_, ?_⟩⟩
      · rw [← hxy, mul_assoc, mul_self_pt, mul_one]
        exact (mem_spanList ss y).mp hy
      · exact (mem_spanList ss _).mpr h1
      · rw [mul_assoc, mul_self_pt, mul_one]

theorem nodup_spanList : ∀ L : List Pt, (spanList L).Nodup
  | [] => List.nodup_singleton _
  | s :: ss => by
    simp only [spanList]
    split_ifs with h
    · exact nodup_spanList ss
    · refine (nodup_spanList ss).append ((nodup_spanList ss).map (mul_left_injective s)) ?_
      intro a ha hb
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      apply h
      rw [List.contains_iff_mem, mem_spanList]
      have := Subgroup.mul_mem _ ((mem_spanList ss y).mp hy) ((mem_spanList ss _).mp ha)
      rwa [← mul_assoc, mul_self_pt, one_mul] at this

@[expose] def IsMask (m : ℕ) (A : Set Pt) : Prop :=
  ∀ u < 256, m.testBit u = true ↔ ptOfCode u ∈ Subgroup.closure A

theorem spanList_length {L : List Pt} {m : ℕ} {A : Set Pt}
    (hA : Subgroup.closure {y | y ∈ L} = Subgroup.closure A) (hm : IsMask m A) :
    (spanList L).length = pop256 m := by
  have hp : (spanList L).Perm (allPts.filter fun p => decide (p ∈ spanList L)) := by
    rw [List.perm_ext_iff_of_nodup (nodup_spanList L) (allPts_nodup.filter _)]
    intro p
    simp [mem_allPts p]
  rw [hp.length_eq, pop256_eq]
  apply len_filter_allPts
  intro w hw
  rw [Bool.eq_iff_iff, decide_eq_true_iff, hm w hw, mem_spanList, hA]

theorem testBit_one' (u : ℕ) : (1 : ℕ).testBit u = decide (u = 0) := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · rfl
  · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt (Nat.one_lt_two_pow hu.ne')]
    simp [hu.ne']

theorem isMask_one : IsMask 1 ∅ := by
  intro u hu
  rw [testBit_one', decide_eq_true_iff, Subgroup.closure_empty, Subgroup.mem_bot, ← ptOfCode_zero,
    ptOfCode_eq_iff hu (by norm_num)]

theorem bfly_facts : ∀ s < 8, ∀ u < 256,
    (u.testBit s = true ∧ 2 ^ s ≤ u ∧ u - 2 ^ s < 256 ∧ (u - 2 ^ s).testBit s = false ∧
      u - 2 ^ s = u ^^^ 2 ^ s) ∨
    (u.testBit s = false ∧ 2 ^ s + u = u ^^^ 2 ^ s ∧
      (¬ 2 ^ s ≤ u ∨ ¬ u - 2 ^ s < 256 ∨ (u - 2 ^ s).testBit s = true)) := by
  decide +kernel

theorem testBit_bfly {s : ℕ} (hs : s < 8) (S : ℕ) {u : ℕ} (hu : u < 256) :
    (bfly s S).testBit u = S.testBit (u ^^^ 2 ^ s) := by
  have hxa : ∀ p q : Bool, (p ^^ (p && q)) = (p && !q) := by decide
  unfold bfly
  simp only [letN_eq, lor_eq, land_eq, xor_eq, shiftLeft_eq, shiftRight_eq, Nat.one_shiftLeft,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_xor, testBit_fullM, testBit_plane hs, hxa]
  rcases bfly_facts s hs u hu with ⟨hb, k3, k4, k5, k6⟩ | ⟨hb, k3, k4⟩
  · rw [← k6]
    simp [hb, hu, k3, k4, k5]
  · rw [← k3]
    by_cases h1 : 2 ^ s ≤ u
    · by_cases h2 : u - 2 ^ s < 256
      · have k5 : (u - 2 ^ s).testBit s = true := by
          rcases k4 with k | k | k
          · exact absurd h1 k
          · exact absurd h2 k
          · exact k
        simp [hb, hu, h1, h2, k5]
      · simp [hb, hu, h2]
    · simp [hb, hu, h1]

theorem xor_mod_two_pow (v k : ℕ) :
    v % 2 ^ (k + 1) = v % 2 ^ k ^^^ (if v.testBit k then 2 ^ k else 0) := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_mod_two_pow]
  split_ifs with h
  · rw [Nat.testBit_two_pow]
    rcases lt_trichotomy n k with hn | rfl | hn
    · simp [hn, show n < k + 1 by omega, hn.ne']
    · simp [h]
    · simp [show ¬ n < k + 1 by omega, show ¬ n < k by omega, show ¬ k = n by omega]
  · rw [Nat.zero_testBit, Bool.xor_false]
    rcases lt_trichotomy n k with hn | rfl | hn
    · simp [hn, show n < k + 1 by omega]
    · simp [h]
    · simp [show ¬ n < k + 1 by omega, show ¬ n < k by omega]

theorem testBit_translK_aux (S v : ℕ) : ∀ k ≤ 8, ∀ u < 256,
    (Nat.rec (motive := fun _ => ℕ) S (fun s T => Bool.rec (motive := fun _ => ℕ) T (bfly s T)
      (Nat.beq (bit v s) (nat_lit 1))) k).testBit u = S.testBit (u ^^^ v % 2 ^ k)
  | 0, _, u, _ => by simp [Nat.mod_one]
  | k + 1, hk, u, hu => by
    change (Bool.rec (motive := fun _ => ℕ) _ (bfly k _) (Nat.beq (bit v k) (nat_lit 1))).testBit u = _
    rw [xor_mod_two_pow]
    cases hv : v.testBit k
    · have e : Nat.beq (bit v k) (nat_lit 1) = false := by rw [bit_eq, hv]; rfl
      rw [e]
      dsimp only
      rw [testBit_translK_aux S v k (by omega) u hu, if_neg Bool.false_ne_true, Nat.xor_zero]
    · have e : Nat.beq (bit v k) (nat_lit 1) = true := by rw [bit_eq, hv]; rfl
      rw [e, if_pos rfl]
      dsimp only
      have hlt : u ^^^ 2 ^ k < 256 := by
        have := Nat.xor_lt_two_pow (n := 8) (by simpa using hu)
          (Nat.pow_lt_pow_right (by norm_num) (by omega : k < 8))
        simpa using this
      rw [testBit_bfly (by omega) _ hu, testBit_translK_aux S v k (by omega) _ hlt,
        Nat.xor_assoc, Nat.xor_comm (2 ^ k)]

theorem testBit_translK (S : ℕ) {v : ℕ} (hv : v < 256) {u : ℕ} (hu : u < 256) :
    (translK S v).testBit u = S.testBit (u ^^^ v) := by
  have h := testBit_translK_aux S v 8 le_rfl u hu
  rw [Nat.mod_eq_of_lt (by simpa using hv)] at h
  exact h

theorem isMask_insV {S : ℕ} {A : Set Pt} (hS : IsMask S A) {v : ℕ} (hv : v < 256) :
    IsMask (insV S v) (insert (ptOfCode v) A) := by
  intro u hu
  rw [mem_closure_insert]
  unfold insV
  rw [bit_eq]
  cases h : S.testBit v
  · change (Nat.lor S (translK S v)).testBit u = true ↔ _
    rw [lor_eq, Nat.testBit_or, Bool.or_eq_true, testBit_translK S hv hu, hS u hu,
      hS _ (Nat.xor_lt_two_pow (n := 8) (by simpa using hu) (by simpa using hv)), ptOfCode_xor]
  · change S.testBit u = true ↔ _
    have hv' := (hS v hv).mp h
    rw [hS u hu]
    refine ⟨Or.inl, fun h1 => h1.elim id fun h2 => ?_⟩
    have := Subgroup.mul_mem _ h2 hv'
    rwa [mul_assoc, mul_self_pt, mul_one] at this

@[expose] def ptsOf (U : ℕ) : Set Pt := {p | ∃ w < 256, U.testBit w = true ∧ ptOfCode w = p}

theorem isMask_spanM_aux (U : ℕ) : ∀ k ≤ 256,
    IsMask (Nat.rec (motive := fun _ => ℕ) (nat_lit 1) (fun w S => Bool.rec (motive := fun _ => ℕ) S
      (insV S w) (Nat.beq (bit U w) (nat_lit 1))) k)
      {p | ∃ w < k, U.testBit w = true ∧ ptOfCode w = p}
  | 0, _ => by
    have e : {p | ∃ w < 0, U.testBit w = true ∧ ptOfCode w = p} = (∅ : Set Pt) := by
      ext p
      simp
    rw [e]
    exact isMask_one
  | k + 1, hk => by
    have ih := isMask_spanM_aux U k (by omega)
    change IsMask (Bool.rec (motive := fun _ => ℕ) _ (insV _ k) (Nat.beq (bit U k) (nat_lit 1))) _
    rw [bit_eq]
    cases h : U.testBit k
    · have e : {p | ∃ w < k + 1, U.testBit w = true ∧ ptOfCode w = p} =
          {p | ∃ w < k, U.testBit w = true ∧ ptOfCode w = p} := by
        ext p
        refine ⟨fun ⟨w, hw, h1, h2⟩ => ⟨w, ?_, h1, h2⟩, fun ⟨w, hw, h1, h2⟩ => ⟨w, by omega, h1, h2⟩⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw | rfl
        · exact hw
        · rw [h] at h1
          exact absurd h1 Bool.false_ne_true
      rw [e]
      exact ih
    · have e : {p | ∃ w < k + 1, U.testBit w = true ∧ ptOfCode w = p} =
          insert (ptOfCode k) {p | ∃ w < k, U.testBit w = true ∧ ptOfCode w = p} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
        refine ⟨fun ⟨w, hw, h1, h2⟩ => ?_, ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw | rfl
          · exact Or.inr ⟨w, hw, h1, h2⟩
          · exact Or.inl h2.symm
        · rintro (rfl | ⟨w, hw, h1, h2⟩)
          · exact ⟨k, by omega, h, rfl⟩
          · exact ⟨w, by omega, h1, h2⟩
      rw [e]
      exact isMask_insV ih (by omega)

theorem isMask_spanM (U : ℕ) : IsMask (spanM U) (ptsOf U) :=
  isMask_spanM_aux U 256 le_rfl

theorem app_mul (v : Mat) (x y : Multiplicative (Fin 4 → ZMod 2)) :
    v.app (x * y) = v.app x * v.app y := by
  simp only [Mat.app, toAdd_mul, Matrix.mulVec_add, ofAdd_add]

theorem act_mul (e : Elt) (p q : Pt) : e.act (p * q) = e.act p * e.act q := by
  unfold Elt.act
  cases e.b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    exact Prod.ext (app_mul _ _ _) (app_mul _ _ _)

@[expose] def commHom (e : Elt) : Pt →* Pt where
  toFun w := e.act w * w⁻¹
  map_one' := by
    have h := act_mul e 1 1
    rw [mul_one] at h
    have h2 : e.act 1 = 1 := by
      have := congrArg (· * (e.act 1)⁻¹) h
      simpa using this.symm
    rw [h2, inv_one, mul_one]
  map_mul' p q := by
    rw [act_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem split_low (u n : ℕ) : u % 2 ^ (n + 1) = u % 2 ^ n ^^^ (if u.testBit n then 2 ^ n else 0) :=
  xor_mod_two_pow u n

theorem commHom_mem (e : Elt) (H : Subgroup Pt)
    (h : ∀ k < 8, commHom e (ptOfCode (2 ^ k)) ∈ H) (w : Pt) : commHom e w ∈ H := by
  obtain ⟨u, hu, rfl⟩ := exists_code_pt w
  have key : ∀ n ≤ 8, commHom e (ptOfCode (u % 2 ^ n)) ∈ H := by
    intro n hn
    induction n with
    | zero =>
      rw [Nat.pow_zero, Nat.mod_one, ptOfCode_zero, map_one]
      exact H.one_mem
    | succ n ih =>
      rw [split_low, ptOfCode_xor, map_mul]
      refine H.mul_mem (ih (by omega)) ?_
      split_ifs
      · exact h n (by omega)
      · rw [ptOfCode_zero, map_one]
        exact H.one_mem
  have := key 8 le_rfl
  rwa [Nat.mod_eq_of_lt (by simpa using hu)] at this

theorem actK_xor_lt (t k : ℕ) (hk : k < 8) : actK t (2 ^ k) ^^^ 2 ^ k < 256 := by
  have := Nat.xor_lt_two_pow (n := 8) (by simpa using actK_lt t (2 ^ k))
    (Nat.pow_lt_pow_right (by norm_num) hk)
  simpa using this

theorem ptOfCode_col (t k : ℕ) :
    ptOfCode (actK t (2 ^ k) ^^^ 2 ^ k) = commHom (decE t) (ptOfCode (2 ^ k)) := by
  rw [ptOfCode_xor, ptOfCode_actK]
  change _ = (decE t).act (ptOfCode (2 ^ k)) * (ptOfCode (2 ^ k))⁻¹
  rw [inv_pt]

@[expose] def colsOf (X : List ℕ) : Set Pt :=
  {p | ∃ v ∈ X, ∃ k < 8, p = commHom (decE (eltX v)) (ptOfCode (2 ^ k))}

theorem mem_colsOf {X : List ℕ} {v : ℕ} (hv : v ∈ X) {k : ℕ} (hk : k < 8) :
    commHom (decE (eltX v)) (ptOfCode (2 ^ k)) ∈ colsOf X := ⟨v, hv, k, hk, rfl⟩

theorem isMask_spanCols :∀ X : List ℕ, IsMask (spanCols X) (colsOf X)
  | [] => by
    have e : colsOf [] = ∅ := by
      ext p
      simp [colsOf]
    rw [e]
    exact isMask_one
  | v :: X => by
    have ih := isMask_spanCols X
    have e0 : spanCols (v :: X) = letN (eltX v) (fun t => Nat.rec (motive := fun _ => ℕ)
        (spanCols X) (fun k S2 => letN (Nat.shiftLeft (nat_lit 1) k) fun e =>
          insV S2 (Nat.xor (actK t e) e)) (nat_lit 8)) := rfl
    rw [e0, letN_eq]
    have inner : ∀ n ≤ 8, IsMask (Nat.rec (motive := fun _ => ℕ) (spanCols X)
        (fun k S2 => letN (Nat.shiftLeft (nat_lit 1) k) fun e =>
          insV S2 (Nat.xor (actK (eltX v) e) e)) n)
        (colsOf X ∪ {p | ∃ k < n, p = commHom (decE (eltX v)) (ptOfCode (2 ^ k))}) := by
      intro n hn
      induction n with
      | zero =>
        have e : colsOf X ∪ {p | ∃ k < 0, p = commHom (decE (eltX v)) (ptOfCode (2 ^ k))} =
            colsOf X := by
          ext p
          simp
        rw [e]
        exact ih
      | succ n ihn =>
        change IsMask (letN (Nat.shiftLeft (nat_lit 1) n) fun e => insV _ (Nat.xor (actK (eltX v) e) e)) _
        rw [letN_eq, shiftLeft_eq, Nat.one_shiftLeft, xor_eq]
        have e : colsOf X ∪ {p | ∃ k < n + 1, p = commHom (decE (eltX v)) (ptOfCode (2 ^ k))} =
            insert (ptOfCode (actK (eltX v) (2 ^ n) ^^^ 2 ^ n))
              (colsOf X ∪ {p | ∃ k < n, p = commHom (decE (eltX v)) (ptOfCode (2 ^ k))}) := by
          rw [ptOfCode_col]
          ext p
          simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff]
          constructor
          · rintro (h | ⟨k, hk, rfl⟩)
            · exact Or.inr (Or.inl h)
            · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
              · exact Or.inr (Or.inr ⟨k, hk, rfl⟩)
              · exact Or.inl rfl
          · rintro (rfl | h | ⟨k, hk, rfl⟩)
            · exact Or.inr ⟨n, by omega, rfl⟩
            · exact Or.inl h
            · exact Or.inr ⟨k, by omega, rfl⟩
        rw [e]
        exact isMask_insV (ihn (by omega)) (actK_xor_lt _ _ (by omega))
    have e : colsOf (v :: X) =
        colsOf X ∪ {p | ∃ k < 8, p = commHom (decE (eltX v)) (ptOfCode (2 ^ k))} := by
      ext p
      simp only [colsOf, Set.mem_union, Set.mem_setOf_eq, List.mem_cons]
      constructor
      · rintro ⟨u, rfl | hu, k, hk, rfl⟩
        · exact Or.inr ⟨k, hk, rfl⟩
        · exact Or.inl ⟨u, hu, k, hk, rfl⟩
      · rintro (⟨u, hu, k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
        · exact ⟨u, Or.inr hu, k, hk, rfl⟩
        · exact ⟨v, Or.inl rfl, k, hk, rfl⟩
    rw [e]
    exact inner 8 le_rfl

theorem closure_commPts (X : List ℕ) :
    Subgroup.closure {y | y ∈ commPts ((X.map eltX).map decE)} = Subgroup.closure (colsOf X) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro p hp
    change p ∈ commPts _ at hp
    unfold commPts at hp
    obtain ⟨e, he, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    exact commHom_mem (decE (eltX v)) _ (fun k hk => Subgroup.subset_closure (mem_colsOf hv hk)) w
  · rw [Subgroup.closure_le]
    rintro p ⟨v, hv, k, hk, rfl⟩
    apply Subgroup.subset_closure
    change _ ∈ commPts _
    unfold commPts
    refine List.mem_flatMap.mpr ⟨decE (eltX v), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨eltX v, List.mem_map_of_mem hv, rfl⟩
    · exact List.mem_map.mpr ⟨_, mem_allPts _, rfl⟩

theorem all_congr' {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem any_congr' {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem fixed_beq (t : ℕ) {w : ℕ} (hw : w < 256) :
    ((decE t).act (ptOfCode w) == ptOfCode w) = (fixK t).testBit w := by
  rw [testBit_fixK t hw, beq_eq_decide]

theorem fixPts_length (G : List ℕ) : (fixPts (G.map decE)).length = pop256 (fixAllK G) := by
  rw [fixPts, pop256_eq]
  apply len_filter_allPts
  intro w hw
  rw [testBit_fixAllK G hw, List.all_map]
  exact all_congr' fun g _ => fixed_beq g hw

theorem mem_fixPts {G : List ℕ} {w : ℕ} (hw : w < 256) :
    ptOfCode w ∈ fixPts (G.map decE) ↔ (fixAllK G).testBit w = true := by
  have hall : ((G.map decE).all fun g => g.act (ptOfCode w) == ptOfCode w) =
      G.all fun g => (fixK g).testBit w := by
    rw [List.all_map]
    exact all_congr' fun g _ => fixed_beq g hw
  rw [fixPts, List.mem_filter, testBit_fixAllK G hw, hall]
  simp [mem_allPts]

theorem fixed1 (x : ℕ) {w : ℕ} (hw : w < 256) :
    ([decE x].all fun g => g.act (ptOfCode w) == ptOfCode w) = (fixK x).testBit w := by
  rw [List.all_cons, List.all_nil, Bool.and_true, fixed_beq x hw]

theorem fixPts₁_length (x : ℕ) : (fixPts₁ [decE x]).length = pop1 (fixK x) := by
  rw [fixPts₁, fixPts, List.filter_filter, ← count_lt16]
  apply len_filter_allPts
  intro w hw
  rw [ptOfCode_snd_eq_one hw, fixed1 x hw, Bool.and_comm]

theorem fixPts₂_length (x : ℕ) : (fixPts₂ [decE x]).length = pop2 (fixK x) := by
  rw [fixPts₂, fixPts, List.filter_filter, ← count_mod16]
  apply len_filter_allPts
  intro w hw
  rw [ptOfCode_fst_eq_one hw, fixed1 x hw, Bool.and_comm]

theorem mem_fixPts₁ (x : ℕ) {w : ℕ} (hw : w < 256) :
    ptOfCode w ∈ fixPts₁ [decE x] ↔ (fixK x).testBit w = true ∧ w < 16 := by
  rw [fixPts₁, fixPts, List.mem_filter, List.mem_filter, ptOfCode_snd_eq_one hw, fixed1 x hw]
  simp [mem_allPts]

theorem mem_fixPts₂ (x : ℕ) {w : ℕ} (hw : w < 256) :
    ptOfCode w ∈ fixPts₂ [decE x] ↔ (fixK x).testBit w = true ∧ w % 16 = 0 := by
  rw [fixPts₂, fixPts, List.mem_filter, List.mem_filter, ptOfCode_fst_eq_one hw, fixed1 x hw]
  simp [mem_allPts]

theorem testBit_w1M (n : ℕ) : w1M.testBit n = decide (n < 16) := by
  change Nat.testBit (2 ^ 16 - 1) n = _
  rw [Nat.testBit_two_pow_sub_one]

theorem testBit_w2M_lt : ∀ n < 256, w2M.testBit n = decide (n % 16 = 0) := by decide +kernel

theorem w2M_lt : w2M < 2 ^ 256 := by decide +kernel

theorem testBit_w2M (n : ℕ) : w2M.testBit n = (decide (n < 256) && decide (n % 16 = 0)) := by
  by_cases hn : n < 256
  · simp [hn, testBit_w2M_lt n hn]
  · simp only [hn, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le w2M_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem pop256_fullM : pop256 fullM = 256 := by decide +kernel

theorem exists_testBit_of_pos {n : ℕ} (h : 0 < n) : ∃ i, n.testBit i = true := by
  by_contra h1
  push Not at h1
  have : n = 0 := Nat.eq_of_testBit_eq fun i => by
    rw [Nat.zero_testBit]
    simpa using h1 i
  omega

theorem testBit_recLorL (f : ℕ → ℕ) (w : ℕ) : ∀ L : List ℕ,
    (List.rec (motive := fun _ => ℕ) (nat_lit 0) (fun x _ acc => Nat.lor acc (f x)) L).testBit w =
      L.any fun x => (f x).testBit w
  | [] => Nat.zero_testBit w
  | x :: L => by
    change (Nat.lor (List.rec (motive := fun _ => ℕ) (nat_lit 0) (fun x _ acc => Nat.lor acc (f x)) L)
      (f x)).testBit w = _
    rw [lor_eq, Nat.testBit_or, testBit_recLorL f w L, List.any_cons, Bool.or_comm]

theorem testBit_boolRec (M : ℕ) (c : Bool) (w : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) M c).testBit w = (c && M.testBit w) := by
  cases c
  · exact Nat.zero_testBit w
  · rfl

theorem testBit_gam2K (X : List ℕ) (w : ℕ) : (gam2K X).testBit w = X.any fun v => X.any fun u =>
    (!(Nat.beq (eltX v) oneE) && (!(Nat.beq (eltX u) oneE) && !(Nat.beq (eltX v) (eltX u)))) &&
      ((maskX v).testBit w && (maskX u).testBit w) := by
  unfold gam2K
  rw [testBit_recLorL]
  refine any_congr' fun v _ => ?_
  rw [testBit_recLorL]
  refine any_congr' fun u _ => ?_
  rw [testBit_boolRec, land_eq, Nat.testBit_and]
  simp only [andB_eq, notB_eq]

theorem testBit_gam3K (X : List ℕ) (w : ℕ) : (gam3K X).testBit w = X.any fun v =>
    (!(Nat.beq (eltX v) oneE) && (maskX v).testBit w) := by
  unfold gam3K
  rw [testBit_recLorL]
  refine any_congr' fun v _ => ?_
  cases Nat.beq (eltX v) oneE
  · rfl
  · exact Nat.zero_testBit w

end CFSG.KC.H9Four.Masks

end
