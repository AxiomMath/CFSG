module

public import Certificates.Data.Kernel.TwoAC.Check
public import CFSG.Certificates.Kernel.BabyMonster.VStripSound

public section

namespace CFSG.KC.BM.TwoAC

open CFSG.KC.BM CFSG.KC.YModel CFSG.KC.BM.SL
open scoped Matrix

theorem stripMat_row (S : List Nat) (t : Fin 4370) : stripMat S t = vrow (rowAtS S t.val) := by
  funext j
  rw [rowAtS, vrow_rowOf]
  rfl

@[expose] def codeAt (Fb : List (List Nat)) (t : Nat) : Nat := (Fb.getD (t / 64) []).getD (t % 64) 0

private theorem natRec_andB_spec (f : Nat → Bool) : ∀ N : Nat,
    Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (f i)) N = true →
      ∀ i < N, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | N + 1, h, i, hi => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (f i)) N)
        (f N) = true := h
    rw [andB_eq, Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact natRec_andB_spec f N h'.1 i hi
    · exact h'.2

private theorem beq_land_one (J j : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight J j) 1) 1 = J.testBit j := by
  rw [nland, nshr, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (J / 2 ^ j) with h | h <;> rw [h] <;> rfl

private def maskOf (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => maskOf b k ||| (if b k then 2 ^ k else 0)

private theorem testBit_maskOf (b : Nat → Bool) : ∀ k i,
    (maskOf b k).testBit i = (decide (i < k) && b i)
  | 0, i => by simp [maskOf]
  | k + 1, i => by
    rw [maskOf, Nat.testBit_lor, testBit_maskOf b k i]
    rcases Nat.lt_trichotomy i k with hik | rfl | hik
    · have h2 : (if b k then 2 ^ k else 0).testBit i = false := by
        split
        · rw [Nat.testBit_two_pow]
          exact decide_eq_false (Nat.ne_of_gt hik)
        · exact Nat.zero_testBit i
      rw [h2, Bool.or_false, decide_eq_true hik, decide_eq_true (Nat.lt_succ_of_lt hik)]
    · rw [decide_eq_false (Nat.lt_irrefl i), Bool.false_and, Bool.false_or,
        decide_eq_true (Nat.lt_succ_self i), Bool.true_and]
      split <;> rename_i hb
      · rw [Nat.testBit_two_pow_self, hb]
      · rw [Nat.zero_testBit]
        cases h : b i
        · rfl
        · exact absurd h hb
    · have h2 : (if b k then 2 ^ k else 0).testBit i = false := by
        split
        · rw [Nat.testBit_two_pow]
          exact decide_eq_false (Nat.ne_of_lt hik)
        · exact Nat.zero_testBit i
      rw [h2, Bool.or_false, decide_eq_false (by omega), decide_eq_false (by omega)]

private theorem maskOf_lt (b : Nat → Bool) : ∀ k, maskOf b k < 2 ^ k
  | 0 => by simp [maskOf]
  | k + 1 => by
    rw [maskOf]
    apply Nat.or_lt_two_pow
    · exact lt_of_lt_of_le (maskOf_lt b k) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
    · split
      · exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
      · exact Nat.two_pow_pos _

private theorem exists_mask {m : Nat} (c : Fin m → ZMod 2) (hc : c ≠ 0) :
    ∃ J : Nat, 0 < J ∧ J < 2 ^ m ∧ ∀ i : Fin m, J.testBit i = decide (c i = 1) := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  let b : Nat → Bool := fun i => if hi : i < m then decide (c ⟨i, hi⟩ = 1) else false
  have hJbit : ∀ i : Fin m, (maskOf b m).testBit i = decide (c i = 1) := by
    intro i
    rw [testBit_maskOf, decide_eq_true i.isLt, Bool.true_and]
    simp only [b, dif_pos i.isLt]
  refine ⟨maskOf b m, Nat.pos_of_ne_zero fun h0 => hc ?_, maskOf_lt b m, hJbit⟩
  funext i
  have e := hJbit i
  rw [h0, Nat.zero_testBit] at e
  rcases h01 (c i) with h | h
  · exact h
  · rw [h] at e
    exact absurd e (by decide)

private theorem vrow_zero : vrow 0 = 0 := by
  funext j
  simp [vrow]

private theorem vrow_xor (a b : Nat) : vrow (a ^^^ b) = vrow a + vrow b := by
  funext j
  simp only [vrow, Nat.testBit_xor, Pi.add_apply, ite_bz, bz_xor]

private theorem vrow_rowOf_xor (a b t : Nat) :
    vrow (rowOf (a ^^^ b) t) = vrow (rowOf a t) + vrow (rowOf b t) := by
  funext j
  simp only [Pi.add_apply, vrow_rowOf, Nat.testBit_xor, bz_xor]

private def Spread (x : Nat) : Prop := ∀ q, x.testBit q = true → q % 64 = 0 ∧ q < 279680

private theorem spread_rowOf (X t : Nat) : Spread (rowOf X t) := by
  intro q hq
  unfold rowOf at hq
  rw [nland, Nat.testBit_and, SM_eq, testBit_SMn, Bool.and_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, decide_eq_true_eq] at hq
  exact ⟨hq.2.2, hq.2.1⟩

private theorem spread_xor {a b : Nat} (ha : Spread a) (hb : Spread b) : Spread (a ^^^ b) := by
  intro q hq
  rw [Nat.testBit_xor] at hq
  cases h : a.testBit q
  · rw [h, Bool.false_xor] at hq
    exact hb q hq
  · exact ha q h

private theorem spread_zero : Spread 0 := fun q hq => by
  rw [Nat.zero_testBit] at hq
  exact absurd hq (by decide)

private theorem eq_zero_of_vrow {x : Nat} (hx : Spread x) (h : vrow x = 0) : x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.zero_testBit]
  cases hq : x.testBit q
  · rfl
  · obtain ⟨h1, h2⟩ := hx q hq
    have hj : q / 64 < 4370 := by omega
    have e := congrFun h ⟨q / 64, hj⟩
    have hq' : 64 * (q / 64) = q := by omega
    simp only [vrow, Pi.zero_apply] at e
    rw [hq', hq] at e
    exact absurd e (by decide)

private theorem blockNodesOK_spec {S SA SB : List Nat} {V0 V1 k : Nat} :
    ∀ (blk : List Nat) (t : Nat), blockNodesOK S SA SB V0 V1 k blk t = true →
      ∀ i < blk.length, nodeOK S SA SB V0 V1 k (t + i) (blk.getD i 0) = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | c :: blk, t, h, i, hi => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (blockNodesOK S SA SB V0 V1 k blk (Nat.succ t)) (nodeOK S SA SB V0 V1 k t c) = true := h
    cases hc : nodeOK S SA SB V0 V1 k t c
    · rw [hc] at h'
      exact (Bool.false_ne_true h').elim
    · rw [hc] at h'
      cases i with
      | zero => simpa using hc
      | succ i =>
        have := blockNodesOK_spec blk (t + 1) h' i (by simp at hi; omega)
        rw [List.getD_cons_succ, show t + (i + 1) = t + 1 + i by omega]
        exact this

private theorem forestBlocks_spec {S SA SB : List Nat} {V0 V1 k : Nat} :
    ∀ (Fb : List (List Nat)) (s : Nat),
      List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun blk _ ih s => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ s))
          (andB (Nat.beq (lenL blk) (rowsS s))
            (blockNodesOK S SA SB V0 V1 k blk (Nat.mul (nat_lit 64) s)))) Fb s = true →
      ∀ i < Fb.length, (Fb.getD i []).length = rowsS (s + i) ∧
        blockNodesOK S SA SB V0 V1 k (Fb.getD i []) (64 * (s + i)) = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | blk :: Fb, s, h, i, hi => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
          (fun blk _ ih s => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ s))
            (andB (Nat.beq (lenL blk) (rowsS s))
              (blockNodesOK S SA SB V0 V1 k blk (Nat.mul (nat_lit 64) s)))) Fb (Nat.succ s))
        (andB (Nat.beq (lenL blk) (rowsS s))
          (blockNodesOK S SA SB V0 V1 k blk (Nat.mul (nat_lit 64) s))) = true := h
    cases hb : andB (Nat.beq (lenL blk) (rowsS s))
        (blockNodesOK S SA SB V0 V1 k blk (Nat.mul (nat_lit 64) s))
    · rw [hb] at h'
      exact (Bool.false_ne_true h').elim
    · rw [hb] at h'
      rw [andB_eq, Bool.and_eq_true] at hb
      cases i with
      | zero =>
        rw [List.getD_cons_zero, Nat.add_zero, ← lenL_eq]
        exact ⟨Nat.eq_of_beq_eq_true hb.1, hb.2⟩
      | succ i =>
        have := forestBlocks_spec Fb (s + 1) h' i (by simp at hi; omega)
        rw [List.getD_cons_succ, show s + (i + 1) = s + 1 + i by omega]
        exact this

theorem forestOK_sound {Fb : List (List Nat)} {S SA SB : List Nat} {V0 V1 k : Nat}
    (h : forestOK Fb S SA SB V0 V1 k = true) : ∀ t < 4370,
      (8740 ≤ codeAt Fb t → codeAt Fb t < 8742 ∧
        rowAtS S t = rowOf (if codeAt Fb t = 8740 then V0 else V1) k) ∧
      (codeAt Fb t < 8740 → codeAt Fb t / 2 < t ∧
        rowAtS S t = rowAtS (if codeAt Fb t % 2 = 0 then SA else SB) (codeAt Fb t / 2)) := by
  have h' : andB (Nat.beq (lenLL Fb) (nat_lit 69))
      (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun blk _ ih s => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ s))
          (andB (Nat.beq (lenL blk) (rowsS s))
            (blockNodesOK S SA SB V0 V1 k blk (Nat.mul (nat_lit 64) s)))) Fb (nat_lit 0)) = true :=
    h
  rw [andB_eq, Bool.and_eq_true] at h'
  have hlen : Fb.length = 69 := by
    rw [← lenLL_eq]
    exact Nat.eq_of_beq_eq_true h'.1
  intro t ht
  obtain ⟨hbl, hbn⟩ := forestBlocks_spec Fb 0 h'.2 (t / 64) (by omega)
  rw [Nat.zero_add] at hbl hbn
  have hrows : rowsS (t / 64) = min 64 (4370 - 64 * (t / 64)) := rowsSn_eq 4370 (t / 64)
  have hnode := blockNodesOK_spec _ _ hbn (t % 64) (by rw [hbl, hrows]; omega)
  rw [Nat.div_add_mod] at hnode
  change nodeOK S SA SB V0 V1 k t (codeAt Fb t) = true at hnode
  generalize codeAt Fb t = c at hnode ⊢
  unfold nodeOK at hnode
  have e1 : Nat.shiftRight c (nat_lit 1) = c / 2 := by
    show c >>> 1 = c / 2
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  cases hble : Nat.ble (nat_lit 8740) c
  ·
    rw [hble] at hnode
    dsimp only at hnode
    rw [andB_eq, Bool.and_eq_true, e1] at hnode
    have hble' : Nat.ble 8740 c = false := hble
    have hc : ¬ 8740 ≤ c := fun hle => by
      have := Nat.ble_eq_true_of_le hle
      rw [hble'] at this
      exact Bool.false_ne_true this
    obtain ⟨h1, h2⟩ := hnode
    refine ⟨fun h => absurd h hc, fun _ => ⟨Nat.le_of_ble_eq_true h1, ?_⟩⟩
    rw [Nat.eq_of_beq_eq_true h2]
    cases hpar : Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1)
    · have hne : c &&& 1 ≠ 1 := Nat.ne_of_beq_eq_false hpar
      rw [Nat.and_one_is_mod] at hne
      rw [if_pos (by omega)]
    · have e : c &&& 1 = 1 := Nat.eq_of_beq_eq_true hpar
      rw [Nat.and_one_is_mod] at e
      rw [if_neg (by omega)]
  ·
    rw [hble] at hnode
    dsimp only at hnode
    rw [andB_eq, Bool.and_eq_true] at hnode
    have hc : 8740 ≤ c := Nat.le_of_ble_eq_true hble
    obtain ⟨h1, h2⟩ := hnode
    have hc2 : c < 8742 := Nat.le_of_ble_eq_true h1
    refine ⟨fun _ => ⟨hc2, ?_⟩, fun h => absurd hc (by omega)⟩
    rw [Nat.eq_of_beq_eq_true h2]
    rcases (by omega : c = 8740 ∨ c = 8741) with rfl | rfl
    · rfl
    · rfl

private theorem combRows_succ (V J m : Nat) :
    combRows V J (m + 1) = combRows V J m ^^^ (if J.testBit m then rowOf V m else 0) := by
  show Nat.xor (combRows V J m) (Bool.rec (motive := fun _ => Nat) 0 (rowOf V m)
    (Nat.beq (Nat.land (Nat.shiftRight J m) 1) 1)) = _
  rw [beq_land_one, nxor]
  cases J.testBit m <;> rfl

private theorem spread_combRows (V J : Nat) : ∀ m, Spread (combRows V J m)
  | 0 => spread_zero
  | m + 1 => by
    rw [combRows_succ]
    refine spread_xor (spread_combRows V J m) ?_
    split
    · exact spread_rowOf V m
    · exact spread_zero

private theorem vrow_combRows (V J : Nat) : ∀ m, vrow (combRows V J m) =
    ∑ j ∈ Finset.range m, if J.testBit j then vrow (rowOf V j) else 0
  | 0 => by
    rw [Finset.sum_range_zero]
    exact vrow_zero
  | m + 1 => by
    rw [combRows_succ, vrow_xor, vrow_combRows V J m, Finset.sum_range_succ]
    congr 1
    split <;> simp [vrow_zero]

theorem rowsNZ_sound {V0 V1 m : Nat} (h : rowsNZ V0 V1 m = true) :
    LinearIndependent (ZMod 2) (fun j : Fin m => (vrow (rowOf V0 j.val), vrow (rowOf V1 j.val))) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg
  have hf0 := congrArg Prod.fst hfg
  have hf1 := congrArg Prod.snd hfg
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd] at hf0 hf1
  have hab : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have hxx : ∀ x : Fin 4370 → ZMod 2, x + x = 0 := by
    intro x
    funext j
    have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h2 (x j)
  suffices hc : f + g = 0 from fun i => hab _ _ (congrFun hc i)
  have hg0 : ∑ i, (f + g) i • vrow (rowOf V0 i) = 0 := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hf0, hxx]
  have hg1 : ∑ i, (f + g) i • vrow (rowOf V1 i) = 0 := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hf1, hxx]
  generalize f + g = c at hg0 hg1 ⊢
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  by_contra hne
  obtain ⟨J, hJ0, hJlt, hJbit⟩ := exists_mask c hne
  have hN : J - 1 < Nat.sub (Nat.shiftLeft 1 m) 1 := by
    rw [nsub, nshl, Nat.one_shiftLeft]
    omega
  have hchk := natRec_andB_spec (fun i => notB (Nat.beq (Nat.lor (combRows V0 (Nat.succ i) m)
      (combRows V1 (Nat.succ i) m)) 0)) _ h (J - 1) hN
  simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel hJ0] at hchk
  have hrow : ∀ V : Nat, (∑ i : Fin m, c i • vrow (rowOf V i)) = 0 → combRows V J m = 0 := by
    intro V hV
    apply eq_zero_of_vrow (spread_combRows V _ m)
    rw [vrow_combRows, Finset.sum_range]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hV
    rw [hJbit i]
    rcases h01 (c i) with e | e <;> simp [e]
  rw [hrow V0 hg0, hrow V1 hg1] at hchk
  exact absurd hchk (by decide)

private theorem testBit_shl_one_sub_one (n q : Nat) :
    (Nat.sub (Nat.shiftLeft 1 n) 1).testBit q = decide (q < n) := by
  rw [nsub, nshl, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

private theorem testBit_LMall (q : Nat) : LMall.testBit q = decide (q < 279680) :=
  testBit_shl_one_sub_one 279680 q

private theorem testBit_testN (S Da Db : List Nat) (Al Ba Bb q : Nat) :
    (testN S Da Db Al Ba Bb).testBit q =
      if q < 279680 then (Nat.xor (mulS S Ba) (mulS Da (mulS S Al))).testBit q
      else (decide (q - 279680 < 279680) &&
        (Nat.xor (mulS S Bb) (mulS Db (mulS S Al))).testBit (q - 279680)) := by
  show (Nat.xor (Nat.land (Nat.xor (mulS S Ba) (mulS Da (mulS S Al))) LMall)
    (Nat.shiftLeft (Nat.land (Nat.xor (mulS S Bb) (mulS Db (mulS S Al))) LMall) 279680)).testBit q
    = _
  simp only [nxor, nland, nshl, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft,
    testBit_LMall]
  by_cases hq : q < 279680
  · have h1 : ¬ 279680 ≤ q := by omega
    simp [hq, h1]
  · have h1 : 279680 ≤ q := by omega
    simp [hq, h1, Bool.and_comm]

private theorem vrow_rowOf_part {S D : List Nat} (hS : wfMat S = true) (hD : wfMat D = true)
    (Al B : Nat) {t : Nat} (ht : t < 64) :
    vrow (rowOf (Nat.xor (mulS S B) (mulS D (mulS S Al))) t) =
      vrow (rowOf B t) ᵥ* stripMat S + (vrow (rowOf Al t) ᵥ* stripMat S) ᵥ* stripMat D := by
  rw [nxor, vrow_rowOf_xor, mulS_rows hS B ht, mulS_rows hD _ ht, mulS_rows hS Al ht]

private theorem bz_testBit_eq_vrow (x q : Nat) (hq : q < 279680) :
    bz (x.testBit q) = vrow (rowOf x (q % 64)) ⟨q / 64, by omega⟩ := by
  rw [vrow_rowOf]
  show bz (x.testBit q) = bz (x.testBit (64 * (q / 64) + q % 64))
  rw [Nat.div_add_mod]

private theorem bz_combL_testBit : ∀ (Ts : List Nat) (J q : Nat),
    bz ((combL Ts J).testBit q) =
      ∑ i ∈ Finset.range Ts.length, bz (J.testBit i) * bz ((Ts.getD i 0).testBit q)
  | [], J, q => by
    show bz ((0 : Nat).testBit q) = _
    simp
  | T :: Ts, J, q => by
    have e : combL (T :: Ts) J = Nat.xor (Bool.rec (motive := fun _ => Nat) 0 T
        (Nat.beq (Nat.land J 1) 1)) (combL Ts (Nat.shiftRight J 1)) := rfl
    have hb : Nat.beq (Nat.land J 1) 1 = J.testBit 0 := beq_land_one J 0
    rw [e, hb, nxor, Nat.testBit_xor, bz_xor, bz_combL_testBit Ts, List.length_cons,
      Finset.sum_range_succ', add_comm (bz _)]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [nshr, Nat.testBit_shiftRight, List.getD_cons_succ, Nat.add_comm 1 i]
    · rw [List.getD_cons_zero]
      cases J.testBit 0 <;> simp

theorem testN_zero {S Da Db : List Nat} {Al Ba Bb : Nat} (hS : wfMat S = true)
    (hA : wfMat Da = true) (hB : wfMat Db = true)
    (h : Nat.beq (testN S Da Db Al Ba Bb) 0 = true) (t : Nat) (ht : t < 64) :
    vrow (rowOf Ba t) ᵥ* stripMat S + (vrow (rowOf Al t) ᵥ* stripMat S) ᵥ* stripMat Da = 0 ∧
      vrow (rowOf Bb t) ᵥ* stripMat S + (vrow (rowOf Al t) ᵥ* stripMat S) ᵥ* stripMat Db = 0 := by
  have h0 : testN S Da Db Al Ba Bb = 0 := Nat.eq_of_beq_eq_true h
  have hU : vrow (rowOf (Nat.xor (mulS S Ba) (mulS Da (mulS S Al))) t) = 0 := by
    funext j
    rw [vrow_rowOf, Pi.zero_apply]
    have hq : 64 * j.val + t < 279680 := by omega
    have e := testBit_testN S Da Db Al Ba Bb (64 * j.val + t)
    rw [h0, Nat.zero_testBit, if_pos hq] at e
    rw [← e]
    rfl
  have hV : vrow (rowOf (Nat.xor (mulS S Bb) (mulS Db (mulS S Al))) t) = 0 := by
    funext j
    rw [vrow_rowOf, Pi.zero_apply]
    have e := testBit_testN S Da Db Al Ba Bb (279680 + (64 * j.val + t))
    rw [h0, Nat.zero_testBit, if_neg (by omega), Nat.add_sub_cancel_left,
      decide_eq_true (by omega : 64 * j.val + t < 279680), Bool.true_and] at e
    rw [← e]
    rfl
  exact ⟨(vrow_rowOf_part hS hA Al Ba ht).symm.trans hU,
    (vrow_rowOf_part hS hB Al Bb ht).symm.trans hV⟩

theorem tests3_sound {S₁ S₂ S₃ Da Db : List Nat} {Al Ba Bb : Nat} (hS₁ : wfMat S₁ = true)
    (hS₂ : wfMat S₂ = true) (hS₃ : wfMat S₃ = true) (hA : wfMat Da = true) (hB : wfMat Db = true)
    (h : combNZ [testN S₁ Da Db Al Ba Bb, testN S₂ Da Db Al Ba Bb, testN S₃ Da Db Al Ba Bb] = true)
    (c : Fin 3 → ZMod 2)
    (hc : ∀ t < 64,
      ∑ i, c i • (vrow (rowOf Ba t) ᵥ* stripMat (![S₁, S₂, S₃] i) +
        (vrow (rowOf Al t) ᵥ* stripMat (![S₁, S₂, S₃] i)) ᵥ* stripMat Da) = 0 ∧
      ∑ i, c i • (vrow (rowOf Bb t) ᵥ* stripMat (![S₁, S₂, S₃] i) +
        (vrow (rowOf Al t) ᵥ* stripMat (![S₁, S₂, S₃] i)) ᵥ* stripMat Db) = 0) :
    c = 0 := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  by_contra hne
  obtain ⟨J, hJ0, hJlt, hJbit⟩ := exists_mask c hne
  have hN : J - 1 < Nat.sub (Nat.shiftLeft 1 (lenL [testN S₁ Da Db Al Ba Bb,
      testN S₂ Da Db Al Ba Bb, testN S₃ Da Db Al Ba Bb])) 1 := by
    show J - 1 < 7
    have : J < 8 := hJlt
    omega
  have hchk := natRec_andB_spec (fun i => notB (Nat.beq (combL [testN S₁ Da Db Al Ba Bb,
      testN S₂ Da Db Al Ba Bb, testN S₃ Da Db Al Ba Bb] (Nat.succ i)) 0)) _ h (J - 1) hN
  simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel hJ0] at hchk
  refine absurd hchk ?_
  suffices hz : combL [testN S₁ Da Db Al Ba Bb, testN S₂ Da Db Al Ba Bb,
      testN S₃ Da Db Al Ba Bb] J = 0 by
    rw [hz]
    decide
  have hSi : ∀ i : Fin 3, wfMat (![S₁, S₂, S₃] i) = true := by
    intro i
    fin_cases i <;> assumption
  have hget : ∀ i : Fin 3, ([testN S₁ Da Db Al Ba Bb, testN S₂ Da Db Al Ba Bb,
      testN S₃ Da Db Al Ba Bb].getD i 0) = testN (![S₁, S₂, S₃] i) Da Db Al Ba Bb := by
    intro i
    fin_cases i <;> rfl
  have hcJ : ∀ i : Fin 3, bz (J.testBit i) = c i := by
    intro i
    rw [hJbit i]
    rcases h01 (c i) with e | e <;> simp [e]
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.zero_testBit]
  apply bz_inj
  rw [bz_combL_testBit, bz_false, List.length_cons, List.length_cons, List.length_singleton,
    Finset.sum_range]
  simp only [hget, hcJ, testBit_testN]
  by_cases hq : q < 279680
  · simp only [if_pos hq]
    have := congrFun (hc (q % 64) (Nat.mod_lt _ (by norm_num))).1 ⟨q / 64, by omega⟩
    rw [Finset.sum_apply, Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, bz_testBit_eq_vrow _ q hq,
      vrow_rowOf_part (hSi i) hA Al Ba (Nat.mod_lt _ (by norm_num))]
  · simp only [if_neg hq]
    by_cases hq2 : q - 279680 < 279680
    · simp only [decide_eq_true hq2, Bool.true_and]
      have := congrFun (hc ((q - 279680) % 64) (Nat.mod_lt _ (by norm_num))).2
        ⟨(q - 279680) / 64, by omega⟩
      rw [Finset.sum_apply, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, bz_testBit_eq_vrow _ _ hq2,
        vrow_rowOf_part (hSi i) hB Al Bb (Nat.mod_lt _ (by norm_num))]
    · simp only [decide_eq_false hq2, Bool.false_and, bz_false, mul_zero, Finset.sum_const_zero]

theorem xorAt_bit (As : List (List Nat)) (s q : Nat) :
    bz ((xorAt As s).testBit q) = (As.map fun A => bz ((lget A s).testBit q)).sum := by
  induction As with
  | nil =>
    change bz ((0 : Nat).testBit q) = _
    simp
  | cons A As ih =>
    change bz ((Nat.xor (lget A s) (xorAt As s)).testBit q) = _
    rw [nxor, Nat.testBit_xor, bz_xor, ih, List.map_cons, List.sum_cons]

theorem xorRowL_sound {T : List Nat} {As : List (List Nat)}
    (h : ∀ s < 69, xorRowL T As s = true) : stripMat T = (As.map stripMat).sum := by
  ext i j
  have e := Nat.eq_of_beq_eq_true (h (i.val / 64) (by omega))
  have key : ∀ L : List (List Nat), (L.map stripMat).sum i j =
      (L.map fun A => bz ((lget A (i.val / 64)).testBit (64 * j.val + i.val % 64))).sum := by
    intro L
    induction L with
    | nil => simp
    | cons A L ih =>
      rw [List.map_cons, List.sum_cons, Matrix.add_apply, ih, List.map_cons, List.sum_cons]
      rfl
  rw [key, ← xorAt_bit, ← e]
  rfl

end CFSG.KC.BM.TwoAC

end
