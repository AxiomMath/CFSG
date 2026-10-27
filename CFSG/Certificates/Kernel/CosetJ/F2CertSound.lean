module

public import CFSG.Sporadic.Co1.Cover.Fox
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Certificates.Kernel.CosetJ.F2Bits

public section

namespace CFSG.KC.CosetJ.F2

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.J4Schreier Matrix

theorem formOK_sound {S₁ S₂ S₃ S₄ a b : Array ℕ}
    (h : formOK S₁.toList S₂.toList S₃.toList S₄.toList a.toList b.toList = true) :
    bigMat S₁ * Rsym + bigMat S₂ * Rdiag + bigMat S₃ * Rinv (colsMatrix a) +
      bigMat S₄ * Rinv (colsMatrix b) = 1 := by
  have hV := Nat.eq_of_beq_eq_true h
  ext ⟨ri, rj⟩ ⟨ci, cj⟩
  have hri := ri.isLt
  have hrj := rj.isLt
  have hci := ci.isLt
  have hcj := cj.isLt
  have hR : 11 * ri.val + rj.val < 121 := by omega
  have hC : 11 * ci.val + cj.val < 121 := by omega
  have key := congrArg
    (fun V => ind (V.testBit (121 * (11 * ri.val + rj.val) + (11 * ci.val + cj.val)))) hV
  simp only at key
  rw [ind_testBit_idPack hC hR le_rfl, ind_testBit_xorN, ← sum_I2] at key
  have hget : ∀ (S : Array ℕ) (n : ℕ), S.toList.getD n 0 = S[n]?.getD 0 := fun S n => by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have hsp : ∀ (S : Array ℕ) (n R : ℕ), R < 2 ^ 121 →
      ind ((spread S.toList n R 121).testBit
        (121 * (11 * ri.val + rj.val) + (11 * ci.val + cj.val))) =
      ind ((S[11 * ri.val + rj.val]?.getD 0).testBit n) *
        ind (R.testBit (11 * ci.val + cj.val)) := fun S n R hRl => by
    rw [testBit_spread hC hRl hR, ind_and, hget]
  have hq : ∀ q : Fin 11 × Fin 11,
      ind ((Nat.xor (spread S₁.toList (11 * q.1.val + q.2.val) (rowSym (11 * q.1.val + q.2.val)) 121)
        (Nat.xor (spread S₂.toList (11 * q.1.val + q.2.val) (rowDiag (11 * q.1.val + q.2.val)) 121)
          (Nat.xor (spread S₃.toList (11 * q.1.val + q.2.val)
            (rowInv a.toList (11 * q.1.val + q.2.val)) 121)
            (spread S₄.toList (11 * q.1.val + q.2.val)
              (rowInv b.toList (11 * q.1.val + q.2.val)) 121)))).testBit
        (121 * (11 * ri.val + rj.val) + (11 * ci.val + cj.val))) =
      bigMat S₁ (ri, rj) q * Rsym q (ci, cj) + bigMat S₂ (ri, rj) q * Rdiag q (ci, cj) +
        bigMat S₃ (ri, rj) q * Rinv (colsMatrix a) q (ci, cj) +
        bigMat S₄ (ri, rj) q * Rinv (colsMatrix b) q (ci, cj) := by
    rintro ⟨qi, qj⟩
    have hqi := qi.isLt
    have hqj := qj.isLt
    have hn : 11 * qi.val + qj.val < 121 := by omega
    simp only [natXor_eq, Nat.testBit_xor, ind_xor]
    rw [hsp _ _ _ (rowSym_lt hn), hsp _ _ _ (rowDiag_lt hn), hsp _ _ _ (rowInv_lt _ hn),
      hsp _ _ _ (rowInv_lt _ hn), ind_testBit_rowSym hqi hqj hci hcj,
      ind_testBit_rowDiag hqj hcj, ind_testBit_rowInv _ hqi hqj hci hcj,
      ind_testBit_rowInv _ hqi hqj hci hcj]
    simp only [hget]
    have eB : ∀ S : Array ℕ, bigMat S (ri, rj) (qi, qj) =
        ind ((S[11 * ri.val + rj.val]?.getD 0).testBit (11 * qi.val + qj.val)) := fun S => rfl
    have eM : ∀ (C : Array ℕ) (x y : Fin 11), colsMatrix C x y = ind ((C[y.val]?.getD 0).testBit x.val) :=
      fun C x y => rfl
    have hsw : ((qj : ℕ) = ci ∧ (qi : ℕ) = cj) ↔ ((ci : ℕ) = qj ∧ (cj : ℕ) = qi) :=
      ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
    rw [eB, eB, eB, eB]
    simp only [Rsym, Rdiag, Rinv, eM, Prod.mk.injEq, Fin.ext_iff, hsw]
    ring
  rw [Finset.sum_congr rfl fun q _ => hq q] at key
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, ← Finset.sum_add_distrib]
  rw [key]
  simp only [idx_eq_iff hrj hcj, Prod.mk.injEq, Fin.ext_iff]

@[expose] def vecN (x : ℕ) (i : Fin 11) : ZMod 2 := ind (x.testBit i.val)

theorem getD_toList (S : Array ℕ) (n : ℕ) : S.toList.getD n 0 = S[n]?.getD 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem colsMatrix_eq (C : Array ℕ) (x y : Fin 11) :
    colsMatrix C x y = ind ((C[y.val]?.getD 0).testBit x.val) := rfl

theorem testBit_and2047 (x i : ℕ) : (x &&& 2047).testBit i = (x.testBit i && decide (i < 11)) := by
  rw [Nat.testBit_and, show (2047 : ℕ) = 2 ^ 11 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem and2047_lt (x : ℕ) : x &&& 2047 < 2 ^ 11 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

theorem mulV_lt (a : List ℕ) (y : ℕ) : mulV a y < 2 ^ 11 := by
  unfold mulV
  refine xorN_lt _ _ _ fun v _ => ?_
  show bit y v * col a v < 2 ^ 11
  rw [mulBit_eq]
  split_ifs
  · exact col_lt a v
  · exact Nat.two_pow_pos _

theorem ind_testBit_mulV (a : Array ℕ) (y : ℕ) (i : Fin 11) :
    ind ((mulV a.toList y).testBit i.val) = ∑ v : Fin 11, colsMatrix a i v * vecN y v := by
  unfold mulV
  rw [ind_testBit_xorN, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun v _ => ?_
  show ind ((bit y v * col a.toList v).testBit i.val) = _
  rw [testBit_mulBit, ind_and, testBit_col _ _ _ i.isLt, getD_toList, colsMatrix_eq, vecN, mul_comm]

theorem foxW_nil (a b : List ℕ) (x : ℕ) : foxW a b [] x = x := rfl

theorem foxW_cons (a b : List ℕ) (c : Bool) (w : List Bool) (x : ℕ) :
    foxW a b (c :: w) x =
      2 ^ 11 * ((foxW a b w x >>> 11) ^^^
          (if c then (foxW a b w x &&& 2047) <<< 11 else foxW a b w x &&& 2047)) +
        (if c then mulV b (foxW a b w x &&& 2047) else mulV a (foxW a b w x &&& 2047)) := by
  have e : foxW a b (c :: w) x =
      (if c then mulV b (foxW a b w x &&& 2047) else mulV a (foxW a b w x &&& 2047)) +
        (((foxW a b w x >>> 11) ^^^
          (if c then (foxW a b w x &&& 2047) <<< 11 else foxW a b w x &&& 2047)) <<< 11) := by
    cases c <;> rfl
  rw [e, Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]

theorem pack_lt {G M : ℕ} (hG : G < 2 ^ 22) (hM : M < 2 ^ 11) : 2 ^ 11 * G + M < 2 ^ 33 := by
  have h1 : 2 ^ 11 * G + M < 2 ^ 11 * (G + 1) := by
    rw [Nat.mul_succ]
    exact Nat.add_lt_add_left hM _
  calc 2 ^ 11 * G + M < 2 ^ 11 * (G + 1) := h1
    _ ≤ 2 ^ 11 * 2 ^ 22 := Nat.mul_le_mul_left _ hG
    _ = 2 ^ 33 := by rw [← Nat.pow_add]

theorem shiftRight11_lt {P : ℕ} (hP : P < 2 ^ 33) : P >>> 11 < 2 ^ 22 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hP)

theorem foxW_spec (a b : Array ℕ) {x : ℕ} (hx : x < 2 ^ 11) : ∀ w : List Bool,
    foxW a.toList b.toList w x < 2 ^ 33 ∧
      (∀ i : Fin 11, ind ((foxW a.toList b.toList w x).testBit i.val) =
        actPos (colsMatrix a) (colsMatrix b) w (vecN x) i) ∧
      (∀ i : Fin 11, ind ((foxW a.toList b.toList w x).testBit (11 + i.val)) =
        (foxVec (colsMatrix a) (colsMatrix b) w (vecN x)).1 i) ∧
      (∀ i : Fin 11, ind ((foxW a.toList b.toList w x).testBit (22 + i.val)) =
        (foxVec (colsMatrix a) (colsMatrix b) w (vecN x)).2 i)
  | [] => by
    have hz : ∀ k, 11 ≤ k → x.testBit k = false := fun k hk =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right Nat.two_pos hk))
    refine ⟨lt_of_lt_of_le hx (by decide), fun i => rfl, fun i => ?_, fun i => ?_⟩
    · rw [foxW_nil, hz _ (by omega)]
      simp [ind, foxVec]
    · rw [foxW_nil, hz _ (by omega)]
      simp [ind, foxVec]
  | c :: w => by
    obtain ⟨hP, hact, hf1, hf2⟩ := foxW_spec a b hx w
    rw [foxW_cons]
    set P := foxW a.toList b.toList w x with hPdef
    have hy : P &&& 2047 < 2 ^ 11 := and2047_lt P
    have hF : P >>> 11 < 2 ^ 22 := shiftRight11_lt hP
    have hyv : ∀ v : Fin 11, vecN (P &&& 2047) v =
        actPos (colsMatrix a) (colsMatrix b) w (vecN x) v := by
      intro v
      rw [← hact v, vecN, testBit_and2047, decide_eq_true v.isLt, Bool.and_true]
    cases c
    ·
      have hM := mulV_lt a.toList (P &&& 2047)
      have hG := Nat.xor_lt_two_pow hF (lt_of_lt_of_le hy (by decide) : P &&& 2047 < 2 ^ 22)
      simp only [Bool.false_eq_true, if_false]
      refine ⟨pack_lt hG hM, fun i => ?_, fun i => ?_, fun i => ?_⟩
      · rw [Nat.testBit_two_pow_mul_add _ hM, if_pos i.isLt, ind_testBit_mulV a _ i]
        simp only [actPos, Bool.false_eq_true, if_false, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun v _ => by rw [hyv v]
      · rw [Nat.testBit_two_pow_mul_add _ hM, if_neg (by omega),
          show 11 + i.val - 11 = i.val by omega, Nat.testBit_xor, ind_xor, Nat.testBit_shiftRight,
          hf1 i, testBit_and2047, decide_eq_true i.isLt, Bool.and_true, hact i]
        simp only [foxVec, Bool.false_eq_true, if_false, Prod.fst_add, Pi.add_apply]
        rw [add_comm]
      · rw [Nat.testBit_two_pow_mul_add _ hM, if_neg (by omega),
          show 22 + i.val - 11 = 11 + i.val by omega, Nat.testBit_xor, ind_xor,
          Nat.testBit_shiftRight, show 11 + (11 + i.val) = 22 + i.val by omega, hf2 i,
          testBit_and2047, decide_eq_false (by omega : ¬ (11 + i.val < 11)), Bool.and_false]
        simp [foxVec, ind]
    ·
      have hM := mulV_lt b.toList (P &&& 2047)
      have hE : (P &&& 2047) <<< 11 < 2 ^ 22 := by
        rw [Nat.shiftLeft_eq]
        calc (P &&& 2047) * 2 ^ 11 < 2 ^ 11 * 2 ^ 11 := Nat.mul_lt_mul_of_pos_right hy (by decide)
          _ = 2 ^ 22 := by rw [← Nat.pow_add]
      have hG := Nat.xor_lt_two_pow hF hE
      simp only [if_true]
      refine ⟨pack_lt hG hM, fun i => ?_, fun i => ?_, fun i => ?_⟩
      · rw [Nat.testBit_two_pow_mul_add _ hM, if_pos i.isLt, ind_testBit_mulV b _ i]
        simp only [actPos, if_true, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun v _ => by rw [hyv v]
      · rw [Nat.testBit_two_pow_mul_add _ hM, if_neg (by omega),
          show 11 + i.val - 11 = i.val by omega, Nat.testBit_xor, ind_xor, Nat.testBit_shiftRight,
          hf1 i, Nat.testBit_shiftLeft, decide_eq_false (by omega : ¬ (i.val ≥ 11)), Bool.false_and]
        simp [foxVec, ind]
      · rw [Nat.testBit_two_pow_mul_add _ hM, if_neg (by omega),
          show 22 + i.val - 11 = 11 + i.val by omega, Nat.testBit_xor, ind_xor,
          Nat.testBit_shiftRight, show 11 + (11 + i.val) = 22 + i.val by omega, hf2 i,
          Nat.testBit_shiftLeft, decide_eq_true (by omega : 11 + i.val ≥ 11), Bool.true_and,
          show 11 + i.val - 11 = i.val by omega, testBit_and2047, decide_eq_true i.isLt,
          Bool.and_true, hact i]
        simp only [foxVec, if_true, Prod.snd_add, Pi.add_apply]
        rw [add_comm]

theorem getW_eq : ∀ (ws : List (List Bool)) (i : ℕ),
    (List.rec (motive := fun _ => Nat → List Bool) (fun _ => [])
      (fun h _ ih i => Nat.rec (motive := fun _ => List Bool) h (fun j _ => ih j) i) ws) i =
      ws.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, j + 1 => getW_eq L j

theorem rowFox_eq (a b : List ℕ) (ws : List (List Bool)) (q : ℕ) :
    rowFox a b ws q = foxW a b (ws.getD (q / 11) []) (2 ^ (q % 11)) >>> 11 := by
  unfold rowFox
  rw [getW_eq, natDiv_eq, natMod_eq, natShiftLeft_eq, Nat.one_shiftLeft]
  rfl

theorem wordsPos_getD (i : Fin 6) : ((List.finRange 6).map wordsPos).getD i.val [] = wordsPos i := by
  simp [List.getD_eq_getElem?_getD]

theorem vecN_two_pow (k : Fin 11) : vecN (2 ^ k.val) = Pi.single k 1 := by
  funext i
  rw [vecN, Nat.testBit_two_pow, ind_decide, Pi.single_apply]
  by_cases h : i = k
  · subst h
    simp
  · rw [if_neg h, if_neg (fun e => h (Fin.ext e.symm))]

theorem rowFox_spec (a b : Array ℕ) (i : Fin 6) (k : Fin 11) :
    rowFox a.toList b.toList ((List.finRange 6).map wordsPos) (11 * i.val + k.val) < 2 ^ 22 ∧
      ∀ c : Fin (11 + 11),
        ind ((rowFox a.toList b.toList ((List.finRange 6).map wordsPos)
          (11 * i.val + k.val)).testBit c.val) =
        flat (foxVec (colsMatrix a) (colsMatrix b) (wordsPos i) (Pi.single k 1)) c := by
  have hk := k.isLt
  rw [rowFox_eq, div_eleven hk, mod_eleven hk, wordsPos_getD]
  have hx : 2 ^ k.val < 2 ^ 11 := Nat.pow_lt_pow_right (by decide) hk
  obtain ⟨hP, -, hf1, hf2⟩ := foxW_spec a b hx (wordsPos i)
  rw [vecN_two_pow] at hf1 hf2
  refine ⟨shiftRight11_lt hP, fun c => ?_⟩
  rw [Nat.testBit_shiftRight]
  induction c using Fin.addCases with
  | left c1 => rw [Fin.coe_castAdd, hf1 c1, flat, Fin.append_left]
  | right c2 =>
    rw [Fin.coe_natAdd, show 11 + (11 + c2.val) = 22 + c2.val by omega, hf2 c2, flat,
      Fin.append_right]

theorem sum_I6 (g : ℕ → ZMod 2) :
    ∑ q : Fin 6 × Fin 11, g (11 * q.1.val + q.2.val) = ∑ n ∈ Finset.range 66, g n := by
  have h1 : ∀ q : Fin 6 × Fin 11, 11 * q.1.val + q.2.val = (finProdFinEquiv q).val := by
    intro q
    show 11 * q.1.val + q.2.val = q.2.val + 11 * q.1.val
    omega
  simp only [h1]
  rw [Equiv.sum_comp finProdFinEquiv (fun k : Fin (6 * 11) => g k.val)]
  exact Fin.sum_univ_eq_sum_range g 66

theorem testBit_rowDelta_lo (a b : List ℕ) {r j : ℕ} (hr : r < 11) (hj : j < 11) :
    (rowDelta a b r).testBit j = ((a.getD r 0).testBit j ^^ decide (r = j)) := by
  have hb : Nat.blt r 11 = true := by rw [Nat.blt_eq]; exact hr
  have e : rowDelta a b r = col a r ^^^ 1 <<< r := by
    unfold rowDelta
    rw [hb]
    rfl
  rw [e, Nat.testBit_xor, testBit_col a r j hj, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_rowDelta_hi (a b : List ℕ) {r j : ℕ} (hr : r < 11) (hj : j < 11) :
    (rowDelta a b (11 + r)).testBit j = ((b.getD r 0).testBit j ^^ decide (r = j)) := by
  have hb : Nat.blt (11 + r) 11 = false := by
    rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
    omega
  have e : rowDelta a b (11 + r) = col b r ^^^ 1 <<< r := by
    unfold rowDelta
    rw [hb]
    show col b (11 + r - 11) ^^^ 1 <<< (11 + r - 11) = _
    rw [Nat.add_sub_cancel_left]
  rw [e, Nat.testBit_xor, testBit_col b r j hj, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem deltaMat_eq (a b : Array ℕ) (r : Fin (11 + 11)) (j : Fin 11) :
    deltaMat (colsMatrix a) (colsMatrix b) r j =
      ind ((rowDelta a.toList b.toList r.val).testBit j.val) := by
  induction r using Fin.addCases with
  | left r1 =>
    dsimp only [deltaMat]
    rw [Fin.append_left, Fin.coe_castAdd, testBit_rowDelta_lo _ _ r1.isLt j.isLt, ind_xor, ind_decide,
      getD_toList, Matrix.add_apply, Matrix.transpose_apply, colsMatrix_eq, Matrix.one_apply]
    simp only [Fin.ext_iff]
  | right r2 =>
    dsimp only [deltaMat]
    rw [Fin.append_right, Fin.coe_natAdd, testBit_rowDelta_hi _ _ r2.isLt j.isLt, ind_xor,
      ind_decide, getD_toList, Matrix.add_apply, Matrix.transpose_apply, colsMatrix_eq,
      Matrix.one_apply]
    simp only [Fin.ext_iff]

theorem ind_testBit_deltaPart (a b X : Array ℕ) {r c : ℕ} (hr : r < 22) (hc : c < 22) :
    ind ((xorN 22 fun r' => (xorN 11 fun j => bit (rowDelta a.toList b.toList r') j *
      (getL X.toList j &&& 4194303)) <<< (22 * r')).testBit (22 * r + c)) =
      ∑ j : Fin 11, ind ((rowDelta a.toList b.toList r).testBit j.val) *
        ind ((X[j.val]?.getD 0).testBit c) := by
  have hin : ∀ r', (xorN 11 fun j => bit (rowDelta a.toList b.toList r') j *
      (getL X.toList j &&& 4194303)) < 2 ^ 22 := by
    intro r'
    refine xorN_lt _ _ _ fun j _ => ?_
    show bit (rowDelta a.toList b.toList r') j * (getL X.toList j &&& 4194303) < 2 ^ 22
    rw [mulBit_eq]
    split_ifs
    · exact lt_of_le_of_lt Nat.and_le_right (by decide)
    · exact Nat.two_pow_pos _
  rw [ind_testBit_xorN]
  have hterm : ∀ r' ∈ Finset.range 22, ind (((xorN 11 fun j => bit (rowDelta a.toList b.toList r') j *
      (getL X.toList j &&& 4194303)) <<< (22 * r')).testBit (22 * r + c)) =
      if r' = r then ind ((xorN 11 fun j => bit (rowDelta a.toList b.toList r) j *
        (getL X.toList j &&& 4194303)).testBit c) else 0 := by
    intro r' _
    rw [testBit_shiftLeft_field hc (hin r'), ind_and, ind_decide]
    split_ifs with h
    · subst h
      rw [one_mul]
    · rw [zero_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range 22) r,
    if_pos (Finset.mem_range.2 hr), ind_testBit_xorN, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [testBit_mulBit, ind_and, Nat.testBit_and, show (4194303 : ℕ) = 2 ^ 22 - 1 from rfl,
    Nat.testBit_two_pow_sub_one, decide_eq_true hc, Bool.and_true, getL_eq, getD_toList]

theorem ind_testBit_foxPart (a b Y : Array ℕ) {r c : ℕ} (hr : r < 22) (hc : c < 22) :
    ind ((xorN 66 fun q => spreadY Y.toList q
      (rowFox a.toList b.toList ((List.finRange 6).map wordsPos) q)).testBit (22 * r + c)) =
      ∑ q : Fin 6 × Fin 11, ind ((Y[r]?.getD 0).testBit (11 * q.1.val + q.2.val)) *
        ind ((rowFox a.toList b.toList ((List.finRange 6).map wordsPos)
          (11 * q.1.val + q.2.val)).testBit c) := by
  rw [ind_testBit_xorN, ← sum_I6]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [testBit_spreadY hc (rowFox_spec a b q.1 q.2).1 hr, ind_and, getD_toList]

theorem foxOK_sound {X Y a b : Array ℕ}
    (h : foxOK X.toList Y.toList a.toList b.toList ((List.finRange 6).map wordsPos) = true) :
    deltaMat (colsMatrix a) (colsMatrix b) * listMat X 11 (11 + 11) +
      (Matrix.of fun (r : Fin (11 + 11)) (c : Fin 6 × Fin 11) =>
        if (Y[r.val]?.getD 0).testBit (11 * c.1.val + c.2.val) then (1 : ZMod 2) else 0) *
      (Matrix.of fun (r : Fin 6 × Fin 11) (c : Fin (11 + 11)) =>
        flat (foxVec (colsMatrix a) (colsMatrix b) (wordsPos r.1) (Pi.single r.2 1)) c) = 1 := by
  have hV : ((xorN 22 fun r => (xorN 11 fun j => bit (rowDelta a.toList b.toList r) j *
      (getL X.toList j &&& 4194303)) <<< (22 * r)) ^^^
      (xorN 66 fun q => spreadY Y.toList q
        (rowFox a.toList b.toList ((List.finRange 6).map wordsPos) q))) = idPack 22 22 :=
    Nat.eq_of_beq_eq_true h
  ext r c
  have hr : r.val < 22 := r.isLt
  have hc : c.val < 22 := c.isLt
  have key := congrArg (fun V => ind (V.testBit (22 * r.val + c.val))) hV
  rw [Nat.testBit_xor, ind_xor, ind_testBit_idPack hc hr le_rfl, ind_testBit_deltaPart a b X hr hc,
    ind_testBit_foxPart a b Y hr hc] at key
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  have e1 : ∑ j : Fin 11, deltaMat (colsMatrix a) (colsMatrix b) r j * listMat X 11 (11 + 11) j c =
      ∑ j : Fin 11, ind ((rowDelta a.toList b.toList r.val).testBit j.val) *
        ind ((X[j.val]?.getD 0).testBit c.val) :=
    Finset.sum_congr rfl fun j _ => by rw [deltaMat_eq]; rfl
  have e2 : ∑ q : Fin 6 × Fin 11,
      (if (Y[r.val]?.getD 0).testBit (11 * q.1.val + q.2.val) then (1 : ZMod 2) else 0) *
        flat (foxVec (colsMatrix a) (colsMatrix b) (wordsPos q.1) (Pi.single q.2 1)) c =
      ∑ q : Fin 6 × Fin 11, ind ((Y[r.val]?.getD 0).testBit (11 * q.1.val + q.2.val)) *
        ind ((rowFox a.toList b.toList ((List.finRange 6).map wordsPos)
          (11 * q.1.val + q.2.val)).testBit c.val) :=
    Finset.sum_congr rfl fun q _ => by rw [(rowFox_spec a b q.1 q.2).2 c]; rfl
  rw [e1, e2, key]
  simp only [Fin.ext_iff]

end CFSG.KC.CosetJ.F2

end
