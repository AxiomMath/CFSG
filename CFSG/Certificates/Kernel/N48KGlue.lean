module

public import Certificates.Data.Kernel.N48K
public import CFSG.Certificates.Kernel.HexaKGlue
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step48NTests

public section

namespace CFSG.KC.N48K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HexaStabK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.N48
open CFSG.ComponentClassification.AS81.HeSylow
open CFSG.KLie.CT (anyN sumN andB orB notB pw2 bit)

theorem bit_eq (X i : Nat) : bit X i = X.testBit i := by
  have h1 : (X >>> i) &&& 1 = X / 2 ^ i % 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 1
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem pw2_eq (c : Nat) : pw2 c = 2 ^ c := by
  change 1 <<< c = 2 ^ c
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem sumMask_spec (f : Nat → Bool) : ∀ k,
    sumN k (fun c => Bool.rec (motive := fun _ => Nat) 0 (pw2 c) (f c)) < 2 ^ k ∧
      ∀ j, (sumN k fun c => Bool.rec (motive := fun _ => Nat) 0 (pw2 c) (f c)).testBit j =
        (decide (j < k) && f j)
  | 0 => ⟨Nat.one_pos, fun j => by
      change Nat.testBit 0 j = _
      simp⟩
  | k + 1 => by
    obtain ⟨hlt, hbit⟩ := sumMask_spec f k
    change Nat.add (Bool.rec (motive := fun _ => Nat) 0 (pw2 k) (f k)) (sumN k _) < _ ∧
      ∀ j, (Nat.add (Bool.rec (motive := fun _ => Nat) 0 (pw2 k) (f k)) (sumN k _)).testBit j = _
    rw [pw2_eq]
    cases hf : f k
    · refine ⟨by simp only [Nat.add_eq, Nat.zero_add]; rw [Nat.pow_succ]; omega, fun j => ?_⟩
      simp only [Nat.add_eq, Nat.zero_add, hbit]
      by_cases hj : j = k
      · subst hj
        simp [hf]
      · by_cases hj' : j < k
        · simp [hj', Nat.lt_succ_of_lt hj']
        · have : ¬ j < k + 1 := by omega
          simp [hj', this]
    · refine ⟨by simp only [Nat.add_eq]; rw [Nat.pow_succ]; omega, fun j => ?_⟩
      simp only [Nat.add_eq]
      rcases Nat.lt_trichotomy j k with h | h | h
      · rw [Nat.testBit_two_pow_add_gt h, hbit]
        simp [h, Nat.lt_succ_of_lt h]
      · subst h
        rw [Nat.testBit_two_pow_add_eq, hbit]
        simp [hf]
      · have hb : 2 ^ k + sumN k (fun c => Bool.rec (motive := fun _ => Nat) 0 (pw2 c) (f c)) <
            2 ^ j := by
          have := Nat.pow_le_pow_right (n := 2) (by omega) (Nat.succ_le_of_lt h)
          rw [Nat.pow_succ] at this
          omega
        rw [Nat.testBit_lt_two_pow hb]
        have : ¬ j < k + 1 := by omega
        simp [this]

@[expose] def TabM (t : Array Bool) (M : Nat) : Prop := ∀ y, t[y]! = M.testBit y

theorem getElem!_ofFn64 (f : Fin 64 → Bool) (y : Nat) :
    (Array.ofFn f)[y]! = if h : y < 64 then f ⟨y, h⟩ else false := by
  split
  · next h =>
    rw [getElem!_pos (Array.ofFn f) y (by simpa using h), Array.getElem_ofFn]
  · next h =>
    rw [getElem!_neg (Array.ofFn f) y (by simpa using h)]
    rfl

variable {w : Nat}

theorem fixTab_tabM (a b : Nat) : TabM (fixTab (unpack 64 w a) (unpack 64 w b)) (fixM w a b) := by
  intro y
  unfold fixTab fixM
  rw [getElem!_ofFn64, (sumMask_spec _ 64).2 y]
  split
  · next h =>
    simp only [h, decide_true, Bool.true_and]
    rw [andB_eq, pgC_eq, pgC_eq, beq_nat, beq_nat]
  · next h => simp [h]

theorem shiftM_testBit (C x j : Nat) :
    (shiftM C x).testBit j = (decide (j < 64) && C.testBit (j ^^^ x)) := by
  unfold shiftM
  rw [(sumMask_spec _ 64).2 j, bit_eq]
  rfl

theorem spanM_rec_testBit (a b C j : Nat) : ∀ k,
    (Nat.rec (motive := fun _ => Nat) C (fun v acc => strictN acc fun acc =>
      Nat.lor acc (Nat.lor (shiftM C (Nat.xor v (pgC 64 w a v)))
        (Nat.lor (shiftM C (Nat.xor v (pgC 64 w b v)))
          (shiftM C (Nat.xor v (pgC 64 w a (pgC 64 w b v))))))) k : Nat).testBit j =
      (C.testBit j || (List.range k).any fun v => decide (j < 64) &&
        (C.testBit (j ^^^ (v ^^^ pgC 64 w a v)) || C.testBit (j ^^^ (v ^^^ pgC 64 w b v)) ||
          C.testBit (j ^^^ (v ^^^ pgC 64 w a (pgC 64 w b v)))))
  | 0 => by simp
  | k + 1 => by
    change (strictN _ fun acc => Nat.lor acc _).testBit j = _
    rw [strictN_eq']
    change Nat.testBit (_ ||| (_ ||| (_ ||| _))) j = _
    rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, spanM_rec_testBit a b C j k,
      shiftM_testBit, shiftM_testBit, shiftM_testBit, List.range_succ, List.any_append,
      List.any_cons, List.any_nil, Bool.or_false]
    cases decide (j < 64) <;> simp [Bool.or_assoc]

theorem spanTab_tabM {a b C : Nat} {t : Array Bool} (ht : TabM t C) (hC : C < 2 ^ 64) :
    TabM (spanTab (unpack 64 w a) (unpack 64 w b) t) (spanM w a b C) := by
  intro y
  unfold spanTab spanM
  rw [getElem!_ofFn64, spanM_rec_testBit]
  split
  · next h =>
    simp only [h, decide_true, Bool.true_and]
    rw [ht y]
    congr 1
    refine any_congr_mem fun v hv => ?_
    have hv' := List.mem_range.1 hv
    rw [ht, ht, ht]
    simp only [Nat.xor_assoc, pgC_eq]
  · next h =>
    have hy : 64 ≤ y := by omega
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hC (Nat.pow_le_pow_right (by omega) hy))]
    simp [h]

theorem fixM_lt (a b : Nat) : fixM w a b < 2 ^ 64 := (sumMask_spec _ 64).1

theorem sumN_eq_sum (k : Nat) (g : Nat → Nat) : sumN k g = ∑ i ∈ Finset.range k, g i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.add (g k) (sumN k g) = _
    rw [ih, Finset.sum_range_succ, Nat.add_eq, Nat.add_comm]

theorem cnt_eq_cntM {t : Array Bool} {M : Nat} (ht : TabM t M) : cnt t = cntM M := by
  unfold cnt cntM popK
  rw [Finset.card_filter, sumN_eq_sum,
    Fin.sum_univ_eq_sum_range (fun i => if t[i]! = true then 1 else 0) 64]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ht i, bit_eq]
  cases M.testBit i <;> rfl

theorem decide_le (a b : Nat) : decide (a ≤ b) = Nat.ble a b := by
  cases h : Nat.ble a b
  · exact decide_eq_false fun h' => by rw [Nat.ble_eq.mpr h'] at h; cases h
  · exact decide_eq_true (Nat.ble_eq.mp h)

theorem fourCheck_eq {a b C S : Nat} {tC tS : Array Bool} (ha : PP 64 w a) (hb : PP 64 w b)
    (hC : TabM tC C) (hS : TabM tS S) :
    fourCheck (unpack 64 w a) (unpack 64 w b) tC tS = fourK w a b C S := by
  unfold fourCheck fourK
  rw [mulN_PP ha hb]
  rw [cnt_eq_cntM (fixTab_tabM (w := w) a a), cnt_eq_cntM (fixTab_tabM (w := w) b b),
    cnt_eq_cntM (fixTab_tabM (w := w) (pcomp 64 w (mask w) a b) (pcomp 64 w (mask w) a b)),
    cnt_eq_cntM hS, cnt_eq_cntM hC, strictB_eq', anyN_eq]
  have hS' : ∀ y, tS[y]! = S.testBit y := hS
  have hC' : ∀ y, tC[y]! = C.testBit y := hC
  simp only [andB_eq, orB_eq, notB_eq, decide_le, blt_eq_decide, bit_eq, pgC_eq, hS', hC',
    Bool.or_assoc, mul]
  rfl

theorem pairCheck_eq {a b : Nat} (ha : PP 64 w a) (hb : PP 64 w b) :
    pairCheck (unpack 64 w a) (unpack 64 w b) = pairK w a b := by
  have hC := fixTab_tabM (w := w) a b
  have hS := spanTab_tabM (w := w) (a := a) (b := b) hC (fixM_lt a b)
  unfold pairCheck pairK
  dsimp only
  rw [strictB_eq', strictB_eq', commN_PP ha hb, eqA_id_PP ha, eqA_id_PP hb, eqA_PP ha hb,
    cnt_eq_cntM hS, fourCheck_eq ha hb hC hS]
  simp only [andB_eq, orB_eq, notB_eq, decide_le, Bool.or_assoc]

theorem invL_rec (w : Nat) (T : Nat → Nat) : ∀ N acc,
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun r ih acc => (fun a => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (a :: acc))
        (Nat.beq (mul 64 w a a) (pidn 64 w))) (T r)) N acc =
      ((List.range N).filter fun j => Nat.beq (mul 64 w (T j) (T j)) (pidn 64 w)).map T ++ acc
  | 0, acc => rfl
  | N + 1, acc => by
    change Bool.rec (motive := fun _ => List Nat) _ _ (Nat.beq (mul 64 w (T N) (T N)) _) = _
    rw [List.range_succ, List.filter_append]
    cases h : Nat.beq (mul 64 w (T N) (T N)) (pidn 64 w)
    · change Nat.rec (motive := fun _ => List Nat → List Nat) _ _ N acc = _
      rw [invL_rec w T N acc]
      simp [h]
    · change Nat.rec (motive := fun _ => List Nat → List Nat) _ _ N (T N :: acc) = _
      rw [invL_rec w T N (T N :: acc)]
      simp [h]

theorem invL_eq (w N : Nat) (T : Nat → Nat) :
    invL w N T = ((List.range N).filter fun j => Nat.beq (mul 64 w (T j) (T j)) (pidn 64 w)).map T :=
  (invL_rec w T N []).trans (List.append_nil _)

theorem mem_invL {N a : Nat} {T : Nat → Nat} (hT : ∀ i < N, PP 64 w (T i)) (ha : a ∈ invL w N T) :
    PP 64 w a := by
  rw [invL_eq] at ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
  exact hT j (List.mem_range.1 (List.mem_filter.1 hj).1)

theorem filter_sq_eq {N : Nat} {T : Nat → Nat} (hT : ∀ i < N, PP 64 w (T i)) :
    ((List.range N).map fun i => unpack 64 w (T i)).filter
        (fun a => eqA 64 (mulN 64 a a) (idA 64)) = (invL w N T).map (unpack 64 w) := by
  rw [invL_eq, List.filter_map, List.map_map]
  change List.map (fun i => unpack 64 w (T i)) _ = List.map (fun i => unpack 64 w (T i)) _
  congr 1
  apply List.filter_congr
  intro j hj
  have ha := hT j (List.mem_range.1 hj)
  simp only [Function.comp_apply]
  rw [mulN_PP ha ha, eqA_id_PP (ha.mul ha)]
  rfl

end CFSG.KC.N48K

end
