module

public import CFSG.Certificates.Kernel.J2H2.Sound

public section

namespace CFSG.KC.J2H2

open CFSG.KD.J2H2 CFSG.KC.Enum
open CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue.H2
open CFSG.RankThree.PartTwo.J2Residue.C4725 CFSG.RankThree.PartTwo.J2Residue.H2S

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem getL_eq {α : Type} (d : α) : ∀ (L : List α) (i : ℕ), getL d L i = L.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => by rw [List.getD_cons_succ, ← getL_eq d L i]; rfl

theorem listLen_eq {α : Type} (L : List α) :
    (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L : ℕ) = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change Nat.succ _ = _
    rw [ih]
    rfl

theorem lbeq_spec : ∀ {L M : List ℕ}, lbeq L M = true → L = M
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | a :: L, b :: M, h => by
    change bAnd(Nat.beq a b, lbeq L M) = true at h
    rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
    rw [beq_true h.1, lbeq_spec h.2]

theorem testBit_mask30 (x b : ℕ) :
    (x &&& 1073741823).testBit b = (x.testBit b && decide (b < 30)) := by
  rw [show (1073741823 : ℕ) = 2 ^ 30 - 1 by norm_num, Nat.testBit_and, Nat.testBit_two_pow_sub_one]

theorem bitZ_selX (R PHV : ℕ) {i : ℕ} (hi : i < 30) :
    bitZ (selX R PHV) i = ∑ m ∈ Finset.range 10, bitZ R m * bitZ PHV (32 * m + i) := by
  have key : ∀ n, bitZ (Nat.rec (motive := fun _ => Nat) 0
      (fun m ih => Nat.xor ih (Nat.mul fld(R, m, 1) fld(PHV, Nat.mul 32 m, 1073741823))) n) i =
      ∑ m ∈ Finset.range n, bitZ R m * bitZ PHV (32 * m + i) := by
    intro n
    induction n with
    | zero =>
      change bitZ 0 i = _
      simp [bitZ]
    | succ n ih =>
      change bitZ (_ ^^^ _) i = _
      rw [bitZ_xor, ih, Finset.sum_range_succ, fld1_eq]
      congr 1
      have hf : (Nat.land (Nat.shiftRight PHV (32 * n)) 1073741823).testBit i =
          PHV.testBit (32 * n + i) := by
        change ((PHV >>> (32 * n)) &&& 1073741823).testBit i = _
        rw [testBit_mask30, Nat.testBit_shiftRight]
        simp [hi]
      by_cases hR : R.testBit n = true
      · simp only [hR, if_true, Nat.mul_eq, one_mul]
        simp only [bitZ, hR, hf, if_true, one_mul]
      · simp [hR, bitZ]
  exact key 10

theorem testBit_bitsL (L : List ℕ) (b : ℕ) : (bitsL L).testBit b = decide (b ∈ L) := by
  induction L with
  | nil =>
    change (0 : ℕ).testBit b = _
    simp
  | cons i L ih =>
    change ((1 <<< i) ||| bitsL L).testBit b = _
    rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp [eq_comm]

theorem bv_mulColsK_aux : ∀ (P : List ℕ) (c x : ℕ),
    bv ((List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun col _ ih c => Nat.xor (Nat.mul fld(x, c, 1) col) (ih (Nat.succ c))) P c : ℕ)) =
      ∑ i ∈ Finset.range P.length, if x.testBit (c + i) then bv (P.getD i 0) else 0
  | [], c, x => by
    change bv 0 = _
    simp [bv_zero]
  | col :: P, c, x => by
    change bv ((Nat.mul fld(x, c, 1) col) ^^^ _) = _
    rw [bv_xor, bv_mulColsK_aux P (c + 1) x, List.length_cons, Finset.sum_range_succ', fld1_eq,
      add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show c + 1 + i = c + (i + 1) by omega, List.getD_cons_succ]
    · by_cases hx : x.testBit c = true
      · simp [hx]
      · simp [hx, bv_zero]

theorem bv_mulColsK {P : List ℕ} (hP : P.length ≤ 12) (x : ℕ) :
    bv (mulColsK P x) = (matOfCols P).mulVec (bv x) := by
  have e : bv (mulColsK P x) = ∑ i ∈ Finset.range P.length,
      if x.testBit (0 + i) then bv (P.getD i 0) else 0 := bv_mulColsK_aux P 0 x
  have hz : ∑ i ∈ Finset.Ico P.length 12, (if x.testBit (0 + i) then bv (P.getD i 0) else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [List.getD_eq_default _ _ (Finset.mem_Ico.1 hi).1, bv_zero, ite_self]
  have hs := Finset.sum_range_add_sum_Ico
    (fun i => if x.testBit (0 + i) then bv (P.getD i 0) else 0) hP
  rw [hz, add_zero] at hs
  rw [e, hs, ← Fin.sum_univ_eq_sum_range]
  funext r
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, matOfCols, Matrix.of_apply, Nat.zero_add]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hx : x.testBit c = true
  · simp [hx, bv]
  · simp [hx, bv]

theorem matMulK_eq (P Q : List ℕ) : matMulK P Q = Q.map (mulColsK P) := by
  induction Q with
  | nil => rfl
  | cons q Q ih =>
    change mulColsK P q :: matMulK P Q = _
    rw [ih, List.map_cons]

theorem matOfCols_matMulK {P : List ℕ} (hP : P.length ≤ 12) (Q : List ℕ) :
    matOfCols (matMulK P Q) = matOfCols P * matOfCols Q := by
  ext r c
  have e := congrFun (bv_mulColsK hP (Q.getD c 0)) r
  have hc : bv ((matMulK P Q).getD c 0) = bv (mulColsK P (Q.getD c 0)) := by
    rw [matMulK_eq]
    by_cases hcq : (c : ℕ) < Q.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hcq), List.getElem_map,
        List.getD_eq_getElem _ _ hcq]
    · rw [List.getD_eq_default _ _ (by simpa using hcq), List.getD_eq_default _ _ (by omega),
        bv_mulColsK hP, bv_zero, Matrix.mulVec_zero]
  simp only [matOfCols, Matrix.of_apply, Matrix.mul_apply] at e ⊢
  rw [hc, e]
  rfl

theorem length_matMulK (P Q : List ℕ) : (matMulK P Q).length = Q.length := by
  rw [matMulK_eq, List.length_map]

theorem matWordK_aux (w : List ℕ) : ∀ acc : List ℕ, acc.length = 12 →
    (List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun j _ ih acc => ih (matMulK acc (Bool.rec (motive := fun _ => List Nat) bCols aCols
        (Nat.beq j 0)))) w acc).length = 12 ∧
    matOfCols (List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun j _ ih acc => ih (matMulK acc (Bool.rec (motive := fun _ => List Nat) bCols aCols
        (Nat.beq j 0)))) w acc) = matOfCols acc * (w.map Mj).prod := by
  induction w with
  | nil => intro acc h; exact ⟨h, by simp⟩
  | cons j w ih =>
    intro acc h
    have hl : (Bool.rec (motive := fun _ => List Nat) bCols aCols (Nat.beq j 0)).length = 12 := by
      cases Nat.beq j 0 <;> rfl
    obtain ⟨h1, h2⟩ := ih (matMulK acc (Bool.rec (motive := fun _ => List Nat) bCols aCols
      (Nat.beq j 0))) (by rw [length_matMulK, hl])
    refine ⟨h1, ?_⟩
    change matOfCols (List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun j _ ih acc => ih (matMulK acc (Bool.rec (motive := fun _ => List Nat) bCols aCols
        (Nat.beq j 0)))) w _) = _
    rw [h2, matOfCols_matMulK (by omega), List.map_cons, List.prod_cons, mul_assoc]
    congr 2
    by_cases hj : j = 0
    · subst hj
      rfl
    · have : Nat.beq j 0 = false := by
        cases hb : Nat.beq j 0
        · rfl
        · exact absurd (beq_true hb) hj
      rw [this, Mj, colsJ, if_neg hj]

theorem matOfCols_id12 : matOfCols id12 = 1 := by
  decide +kernel

theorem matOfCols_matWordK (w : List ℕ) :
    (matWordK aCols bCols w).length = 12 ∧
      matOfCols (matWordK aCols bCols w) = matOfCols (matWord w) := by
  obtain ⟨h1, h2⟩ := matWordK_aux w id12 rfl
  refine ⟨h1, ?_⟩
  change matOfCols (List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun j _ ih acc => ih (matMulK acc (Bool.rec (motive := fun _ => List Nat) bCols aCols
        (Nat.beq j 0)))) w id12) = _
  rw [h2, matOfCols_id12, one_mul, matOfCols_matWord]

theorem matWordInvK_aux (w : List ℕ) : ∀ acc : List ℕ,
    matOfCols (List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun j _ ih acc => ih (matMulK (Bool.rec (motive := fun _ => List Nat) (matMulK bCols bCols)
        aCols (Nat.beq j 0)) acc)) w acc) =
      (w.reverse.map fun j => matOfCols (invColsJ j)).prod * matOfCols acc := by
  induction w with
  | nil => intro acc; simp
  | cons j w ih =>
    intro acc
    have hl : (Bool.rec (motive := fun _ => List Nat) (matMulK bCols bCols) aCols
        (Nat.beq j 0)).length ≤ 12 := by
      cases Nat.beq j 0 <;> decide
    change matOfCols (List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun j _ ih acc => ih (matMulK (Bool.rec (motive := fun _ => List Nat) (matMulK bCols bCols)
        aCols (Nat.beq j 0)) acc)) w _) = _
    rw [ih, matOfCols_matMulK hl, List.reverse_cons, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, mul_assoc]
    congr 2
    by_cases hj : j = 0
    · subst hj
      rfl
    · have : Nat.beq j 0 = false := by
        cases hb : Nat.beq j 0
        · rfl
        · exact absurd (beq_true hb) hj
      rw [this, invColsJ, if_neg hj, matOfCols_matMulK (by decide), matOfCols_mulColsMat]

theorem bitZ_fieldAt (V h t : ℕ) (ht : t < 384) : bitZ (fieldAt V h) t = bitZ V (384 * h + t) := by
  simp only [bitZ, testBit_fieldAt, decide_eq_true ht, Bool.and_true]

theorem bv_hv (HP j x t : ℕ) (c : Fin 12) :
    bv (hv HP j x t) c = bitZ (rowAt HP x) (384 * t + (32 * c + j)) := by
  simp only [bv, hv, bitZ, testBit_hvR, decide_eq_true c.isLt, Bool.true_and]

theorem fieldAt_lt (V h : ℕ) : fieldAt V h < 2 ^ 384 := by
  change (V >>> (384 * h)) &&& ((1 <<< 384) - 1) < 2 ^ 384
  rw [Nat.one_shiftLeft]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)

theorem bitZ_rep (Q b : ℕ) {h t : ℕ} (hh : h < 128) (ht : t < 384) :
    bitZ (fieldAt Q b * repN) (384 * h + t) = bitZ Q (384 * b + t) := by
  have e1 : (384 * h + t) / 384 = h := by omega
  have e2 : (384 * h + t) % 384 = t := by omega
  unfold bitZ
  rw [Nat.mul_comm, testBit_repN_mul _ _ (fieldAt_lt Q b), e1, e2, decide_eq_true hh, Bool.true_and,
    testBit_fieldAt, decide_eq_true ht, Bool.and_true]

theorem spyK_spec {SP : List (List ℕ)} (hsp : spyK SP aCols bCols yWords = true)
    (hSP : ∀ k < 3, (getL [] SP k).length = 12) {k : ℕ} (hk : k < 3) :
    getL [] SP k = (matWordK aCols bCols (getL [] yWords k)).map spread := by
  have h : spRowK (getL [] SP k) (matWordK aCols bCols (getL [] yWords k)) = true :=
    CFSG.KS.PK.allN_iff.1 hsp k hk
  have hl := (matOfCols_matWordK (getL [] yWords k)).1
  apply List.ext_getElem
  · rw [List.length_map, hl, hSP k hk]
  · intro c h1 _
    have hc : c < 12 := by rw [hSP k hk] at h1; exact h1
    have e : getL 0 (getL [] SP k) c = spread (getL 0 (matWordK aCols bCols (getL [] yWords k)) c) :=
      beq_true (CFSG.KS.PK.allN_iff.1 h c hc)
    rw [getL_eq 0 (getL [] SP k) c, getL_eq 0 (matWordK aCols bCols (getL [] yWords k)) c,
      List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ (by rw [hl]; exact hc)] at e
    rw [e, List.getElem_map]

theorem and31 (e : ℕ) : Nat.land e 31 = e % 32 := Nat.and_two_pow_sub_one_eq_mod e 5

theorem shr5 (e : ℕ) : Nat.shiftRight e 5 = e / 32 := Nat.shiftRight_eq_div_pow e 5

theorem covWalk {IND : List ℕ} : ∀ {DEPA : List ℕ}, (List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(Nat.blt (Nat.land e 31) 30,
      bAnd(Nat.beq (Nat.land (Nat.shiftRight e 5) (bitsL IND)) (Nat.shiftRight e 5), ih))) DEPA) = true →
    ∀ e ∈ DEPA, e % 32 < 30 ∧ e / 32 &&& bitsL IND = e / 32
  | [], _ => fun e he => absurd he List.not_mem_nil
  | e :: D, h => by
    change bAnd(Nat.blt (Nat.land e 31) 30, bAnd(Nat.beq (Nat.land (Nat.shiftRight e 5) (bitsL IND))
      (Nat.shiftRight e 5), _)) = true at h
    simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [and31] at h1
      have := beq_true h2
      rw [shr5] at this
      exact ⟨h1, this⟩
    · exact covWalk h3 x hx

theorem covK_parts {IND DEPA : List ℕ} {BR : ℕ} (h : covK IND DEPA BR = true) :
    bitsL IND &&& depBits DEPA = 0 ∧ bitsL IND ||| depBits DEPA = 1073741823 ∧ fieldAt BR 0 = 0 ∧
      ∀ e ∈ DEPA, e % 32 < 30 ∧ e / 32 &&& bitsL IND = e / 32 := by
  unfold covK at h
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.bAnd_eq, Bool.and_eq_true,
    CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨beq_true h1, beq_true h2, beq_true h3, covWalk h4⟩

theorem testBit_L0 (q : ℕ) : (repN * spread 4095).testBit q =
    (decide (q / 384 < 128) && decide (q % 384 % 32 = 0 ∧ q % 384 / 32 < 12)) := by
  have hl : spread 4095 < 2 ^ 384 :=
    lt_of_lt_of_le (spread_lt 4095) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  rw [testBit_repN_mul _ _ hl, testBit_spread]
  by_cases h : q % 384 % 32 = 0 ∧ q % 384 / 32 < 12
  · rw [decide_eq_true h, show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one,
      decide_eq_true h.2]
    rfl
  · rw [decide_eq_false h]
    simp

theorem bitZ_and_L0dep {dep Q t r j : ℕ} (hdep : dep < 2 ^ 30) (hjd : dep.testBit j = true)
    (ht : t < 128) (hr : r < 12) (hj : j < 30) :
    bitZ (Q &&& repN * spread 4095 * dep) (384 * t + (32 * r + j)) =
      bitZ Q (384 * t + (32 * r + j)) := by
  have hl : spread 4095 * dep < 2 ^ 384 :=
    calc _ < 2 ^ 353 * 2 ^ 30 := Nat.mul_lt_mul'' (spread_lt 4095) hdep
      _ ≤ 2 ^ 384 := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have e1 : (384 * t + (32 * r + j)) / 384 = t := by omega
  have e2 : (384 * t + (32 * r + j)) % 384 = 32 * r + j := by omega
  have hx : ∀ h, dep / 2 ^ (384 * h) % 2 ^ 384 < 2 ^ 30 := fun h =>
    lt_of_le_of_lt (le_trans (Nat.mod_le _ _) (Nat.div_le_self _ _)) hdep
  have hs := testBit_spread_mul (v := 4095) hx (h := 0) hr hj
  rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add] at hs
  unfold bitZ
  rw [Nat.testBit_and, Nat.mul_assoc, testBit_repN_mul _ _ hl, e1, e2, decide_eq_true ht,
    Bool.true_and, Nat.mul_comm (spread 4095), hs, hjd,
    show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one, decide_eq_true hr]
  simp

theorem bitZ_permF (V T o : ℕ) {t s : ℕ} (ht : t < 128) (hs : s < 384) :
    bitZ (permF V T o) (384 * t + s) = bitZ V (384 * pg 7 127 T (o + t) + s) := by
  have key : ∀ n q, (Nat.rec (motive := fun _ => Nat) 0 (fun h ih => Nat.lor ih (Nat.shiftLeft
      (fieldAt V (pg 7 127 T (Nat.add o h))) (Nat.mul 384 h))) n : ℕ).testBit q =
      (decide (q < 384 * n) && (fieldAt V (pg 7 127 T (o + q / 384))).testBit (q % 384)) := by
    intro n q
    induction n with
    | zero =>
      change (0 : ℕ).testBit q = _
      simp
    | succ n ih =>
      change (_ ||| _ <<< (384 * n) : ℕ).testBit q = _
      rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases h1 : q < 384 * n
      · have h2 : ¬ 384 * n ≤ q := by omega
        have h3 : q < 384 * (n + 1) := by omega
        simp [h1, h2, h3]
      · by_cases h3 : q < 384 * (n + 1)
        · have h4 : q / 384 = n := by omega
          have h5 : q - 384 * n = q % 384 := by omega
          simp only [decide_eq_false h1, Bool.false_and, Bool.false_or, decide_eq_true h3,
            Bool.true_and, decide_eq_true (show 384 * n ≤ q by omega), h4, h5]
          rfl
        · have h6 : (fieldAt V (pg 7 127 T (o + n))).testBit (q - 384 * n) = false :=
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (fieldAt_lt _ _)
              (Nat.pow_le_pow_right (by norm_num) (by omega)))
          simp [h1, h3, h6]
  have ek : (permF V T o).testBit (384 * t + s) = _ := key 128 (384 * t + s)
  unfold bitZ
  rw [ek, testBit_fieldAt]
  have e1 : (384 * t + s) / 384 = t := by omega
  have e2 : (384 * t + s) % 384 = s := by omega
  rw [e1, e2, decide_eq_true (show 384 * t + s < 384 * 128 by omega), decide_eq_true hs]
  simp

theorem bitZ_shl (x s q : ℕ) : bitZ (x <<< s) q = if s ≤ q then bitZ x (q - s) else 0 := by
  unfold bitZ
  rw [Nat.testBit_shiftLeft]
  by_cases h : s ≤ q
  · simp [h]
  · simp [h]

theorem bitZ_mixOne (A Q q : ℕ) :
    bitZ (mixOne A Q (repN * spread 4095)) q = ∑ i ∈ Finset.range 30,
      bitZ A i * (if (repN * spread 4095).testBit q then bitZ Q (i + q) else 0) := by
  have key : ∀ n, bitZ (Nat.rec (motive := fun _ => Nat) 0
      (fun i ih => Nat.xor ih (nIf(Nat.beq fld(A, i, 1) 1,
        Nat.land (Nat.shiftRight Q i) (repN * spread 4095), 0))) n) q = ∑ i ∈ Finset.range n,
      bitZ A i * (if (repN * spread 4095).testBit q then bitZ Q (i + q) else 0) := by
    intro n
    induction n with
    | zero =>
      change bitZ 0 q = _
      simp [bitZ]
    | succ n ih =>
      change bitZ (_ ^^^ _) q = _
      rw [bitZ_xor, ih, Finset.sum_range_succ, fld1_eq, CFSG.KS.PK.nIf_eq]
      congr 1
      by_cases hA : A.testBit n = true
      · have hb : Nat.beq (if A.testBit n = true then 1 else 0) 1 = true := by rw [if_pos hA]; rfl
        rw [if_pos hb]
        change bitZ ((Q >>> n) &&& repN * spread 4095) q = _
        unfold bitZ
        rw [Nat.testBit_and, Nat.testBit_shiftRight, if_pos hA, one_mul]
        cases (repN * spread 4095).testBit q <;> simp
      · have hb : Nat.beq (if A.testBit n = true then 1 else 0) 1 = false := by rw [if_neg hA]; rfl
        rw [if_neg (by rw [hb]; decide)]
        unfold bitZ
        rw [if_neg hA, zero_mul]
        simp
  exact key 30

theorem bitZ_mixK (DEPA : List ℕ) (Q : ℕ) {t r j : ℕ} (ht : t < 128) (hr : r < 12) (hj : j < 30) :
    bitZ (mixK DEPA Q (repN * spread 4095)) (384 * t + (32 * r + j)) = ∑ i ∈ Finset.range 30,
      (DEPA.map fun e => if e % 32 = j then bitZ (e / 32) i else 0).sum *
        bitZ Q (384 * t + (32 * r + i)) := by
  induction DEPA with
  | nil =>
    change bitZ 0 _ = _
    simp [bitZ]
  | cons e D ih =>
    change bitZ (mixK D Q (repN * spread 4095) ^^^
      mixOne (Nat.shiftRight e 5) Q (repN * spread 4095) <<< Nat.land e 31) _ = _
    rw [bitZ_xor, ih, bitZ_shl, and31, shr5, bitZ_mixOne]
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    suffices hB : (if e % 32 ≤ 384 * t + (32 * r + j) then ∑ i ∈ Finset.range 30, bitZ (e / 32) i *
        (if (repN * spread 4095).testBit (384 * t + (32 * r + j) - e % 32) = true then
          bitZ Q (i + (384 * t + (32 * r + j) - e % 32)) else 0) else 0) =
        ∑ i ∈ Finset.range 30, (if e % 32 = j then bitZ (e / 32) i else 0) *
          bitZ Q (384 * t + (32 * r + i)) by
      rw [hB, add_comm]
    by_cases hej : e % 32 = j
    · rw [if_pos (by omega)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hq : 384 * t + (32 * r + j) - e % 32 = 384 * t + 32 * r := by omega
      rw [hq, testBit_L0, if_pos hej]
      have h1 : (384 * t + 32 * r) / 384 < 128 := by omega
      have h2 : (384 * t + 32 * r) % 384 % 32 = 0 ∧ (384 * t + 32 * r) % 384 / 32 < 12 := by omega
      rw [decide_eq_true h1, decide_eq_true h2, Bool.and_true, if_pos rfl,
        show i + (384 * t + 32 * r) = 384 * t + (32 * r + i) by omega]
    · have hz : ∑ i ∈ Finset.range 30, (if e % 32 = j then bitZ (e / 32) i else 0) *
          bitZ Q (384 * t + (32 * r + i)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [if_neg hej, zero_mul]
      rw [hz]
      by_cases hle : e % 32 ≤ 384 * t + (32 * r + j)
      · rw [if_pos hle]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [testBit_L0]
        have : ¬ ((384 * t + (32 * r + j) - e % 32) % 384 % 32 = 0 ∧
            (384 * t + (32 * r + j) - e % 32) % 384 / 32 < 12) := by omega
        rw [decide_eq_false this, Bool.and_false, if_neg Bool.false_ne_true, mul_zero]
      · rw [if_neg hle]

theorem coc_num
    {HP LMP MTP GP PP : ℕ} {SP : List (List ℕ)}
    (hrow : ∀ i < 384, rowOKf HP repN LMP MTP SP i = true)
    (hd : dataK GP PP LMP genT parT lT = true) (hmt : mtK MTP LMP GP PP = true)
    (hsp : spyK SP aCols bCols yWords = true) (hSP : ∀ k < 3, (getL [] SP k).length = 12) :
    ∀ j < 30, ∀ k < 3, ∀ b < 128, ∀ h < 128,
      (matOfCols (yCols k)).mulVec (bv (hv HP j b h)) + bv (hv HP j (lmul k b) h) +
        bv (hv HP j (k + 1) (mulIdx b h)) + bv (hv HP j (k + 1) b) = 0 := by
  intro j hj k hk b hb h hh
  obtain ⟨-, -, hl⟩ := data_spec hd
  have hr := hrow (128 * k + b) (by omega)
  have e1 : (128 * k + b) / 128 = k := by omega
  have e2 : (128 * k + b) % 128 = b := by omega
  change rowOK HP repN LMP MTP SP ((128 * k + b) / 128) ((128 * k + b) % 128) = true at hr
  rw [e1, e2] at hr
  unfold rowOK rowQ rowFin at hr
  have hF := beq_true (CFSG.KS.PK.allN_iff.1 hr h hh)
  have hX : fieldAt ((mulRowK (getL [] SP k) (rowAt HP b) (repN * 1073741823) ^^^
      rowAt HP (lmul k b)) ^^^ fieldAt (rowAt HP (k + 1)) b * repN) h =
      fieldAt (rowAt HP (k + 1)) (mulIdx b h) := by
    rw [← hl k hk b hb, ← mt_spec hmt hd b hb h hh]
    exact hF
  have hV := spyK_spec hsp hSP hk
  have hlV := (matOfCols_matWordK (getL [] yWords k)).1
  have hm : matOfCols (matWordK aCols bCols (getL [] yWords k)) = matOfCols (yCols k) := by
    rw [(matOfCols_matWordK _).2, yCols, nth_eq_getD, getL_eq]
  funext r
  have hrr := r.isLt
  have hq : 32 * (r : ℕ) + j < 384 := by omega
  have eb : bitZ (fieldAt ((mulRowK (getL [] SP k) (rowAt HP b) (repN * 1073741823) ^^^
      rowAt HP (lmul k b)) ^^^ fieldAt (rowAt HP (k + 1)) b * repN) h) (32 * r + j) =
      bitZ (fieldAt (rowAt HP (k + 1)) (mulIdx b h)) (32 * r + j) := by rw [hX]
  rw [bitZ_fieldAt _ _ _ hq, bitZ_fieldAt _ _ _ hq, bitZ_xor, bitZ_xor,
    bitZ'_mulRowK hV _ hh hrr hj, bitZ_rep _ _ hh hq, hlV] at eb
  simp only [Pi.add_apply, Pi.zero_apply, bv_hv]
  have hs : (matOfCols (yCols k)).mulVec (bv (hv HP j b h)) r = ∑ i ∈ Finset.range 12,
      bitZ ((matWordK aCols bCols (getL [] yWords k)).getD i 0) r *
        bitZ (rowAt HP b) (384 * h + (32 * i + j)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => bitZ ((matWordK aCols bCols (getL [] yWords k)).getD i 0) r *
        bitZ (rowAt HP b) (384 * h + (32 * i + j))), ← hm]
    simp only [Matrix.mulVec, dotProduct, matOfCols, Matrix.of_apply, bv_hv]
    rfl
  rw [hs]
  set S := ∑ i ∈ Finset.range 12, bitZ ((matWordK aCols bCols (getL [] yWords k)).getD i 0) r *
    bitZ (rowAt HP b) (384 * h + (32 * i + j))
  have h2 := CharTwo.add_self_eq_zero (S + bitZ (rowAt HP (lmul k b)) (384 * h + (32 * r + j)) +
    bitZ (rowAt HP (k + 1)) (384 * b + (32 * r + j)))
  rw [← eb]
  linear_combination h2

theorem isNormCoc_Hc
    {HP LMP MTP GP PP : ℕ} {SP : List (List ℕ)}
    (hrow : ∀ i < 384, rowOKf HP repN LMP MTP SP i = true) (hn : normK HP = true)
    (hd : dataK GP PP LMP genT parT lT = true) (hmt : mtK MTP LMP GP PP = true)
    (hsp : spyK SP aCols bCols yWords = true) (hSP : ∀ k < 3, (getL [] SP k).length = 12)
    {ρ : ↥P →* Module.End (ZMod 2) V12} (hρ : IsMRep ρ)
    {j : ℕ} (hj : j < 30) : IsNormCoc (rhoS ρ) (Hc HP j) := by
  have hc := coc_num hrow hd hmt hsp hSP j hj
  have hz := norm_num' hn j hj
  refine isNormCoc_of_gen (rhoS ρ) (fun t => ?_) (fun k hk s t => ?_) (fun s => ?_)
  · rw [Hc, idx_one', (hz _ (idx_lt t)).1, bv_zero]
  · obtain ⟨b, hb, rfl⟩ := elt_surjective s
    obtain ⟨h, hh, rfl⟩ := elt_surjective t
    obtain ⟨hl, hle⟩ := lmul_spec hk hb
    obtain ⟨hm, hme⟩ := mulIdx_spec (a := b) hh
    have hy : yS k = elt (k + 1) := (elt_succ hk).symm
    rw [defect, ← hle, ← hme, hy, Hc_elt HP j hb hh, Hc_elt HP j hl hh,
      Hc_elt HP j (by omega) hm, Hc_elt HP j (by omega) hb, ← hy, rhoS_yS hρ hk]
    have e := hc k hk b hb h hh
    rw [sub_eq_add_neg, sub_eq_add_neg, neg_eq_self_zmod2, neg_eq_self_zmod2]
    exact e
  · rw [Hc, idx_one', (hz _ (idx_lt s)).2, bv_zero]

theorem rel_num {HP LMP BR GP PP : ℕ} {SP : List (List ℕ)} {IND DEPA : List ℕ}
    (hrel : ∀ k < 3, relK HP repN LMP BR SP DEPA k = true) (hcov : covK IND DEPA BR = true)
    (hd : dataK GP PP LMP genT parT lT = true)
    (hsp : spyK SP aCols bCols yWords = true) (hSP : ∀ k < 3, (getL [] SP k).length = 12) :
    (∀ i ∈ IND, i < 30) ∧ (∀ j < 30, bv (hvR BR j 0) = 0) ∧
    ∀ j < 30, j ∉ IND → ∃ A ⊆ IND.toFinset, ∀ k < 3, ∀ t < 128,
      bv (hv HP j (k + 1) t) = ∑ i ∈ A, bv (hv HP i (k + 1) t) +
        ((matOfCols (yCols k)).mulVec (bv (hvR BR j t)) + bv (hvR BR j (lmul k t)) +
          bv (hvR BR j (k + 1))) := by
  obtain ⟨-, -, hl⟩ := data_spec hd
  obtain ⟨h1, h2, h3, h4⟩ := covK_parts hcov
  have hI : ∀ i ∈ IND, i < 30 := fun i hi => by
    have e := congrArg (fun z => Nat.testBit z i) h2
    simp only [Nat.testBit_or, testBit_bitsL, decide_eq_true hi, Bool.true_or] at e
    rw [show (1073741823 : ℕ) = 2 ^ 30 - 1 by norm_num, Nat.testBit_two_pow_sub_one] at e
    exact of_decide_eq_true e.symm
  refine ⟨hI, fun j hj => by rw [hvR_zero_of_fieldAt h3 hj, bv_zero], fun j hj hjI => ?_⟩
  have hjd : (depBits DEPA).testBit j = true := by
    have e := congrArg (fun z => Nat.testBit z j) h2
    simp only [Nat.testBit_or, testBit_bitsL, decide_eq_false hjI, Bool.false_or] at e
    rw [show (1073741823 : ℕ) = 2 ^ 30 - 1 by norm_num, Nat.testBit_two_pow_sub_one,
      decide_eq_true hj] at e
    exact e
  have hdep : depBits DEPA < 2 ^ 30 := by
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    have e := congrArg (fun z => Nat.testBit z i) h2
    simp only [Nat.testBit_or] at e
    rw [show (1073741823 : ℕ) = 2 ^ 30 - 1 by norm_num, Nat.testBit_two_pow_sub_one,
      decide_eq_false (by omega)] at e
    cases hb : (depBits DEPA).testBit i
    · rfl
    · rw [hb, Bool.or_true] at e
      exact absurd e (by decide)
  set c : ℕ → ZMod 2 := fun i => (DEPA.map fun e => if e % 32 = j then bitZ (e / 32) i else 0).sum
    with hc
  have hc01 : ∀ i, c i = 0 ∨ c i = 1 := fun i => by
    generalize c i = z
    revert z
    decide
  refine ⟨(Finset.range 30).filter fun i => c i = 1, fun i hi => ?_, fun k hk t ht => ?_⟩
  · obtain ⟨hi30, hci⟩ := Finset.mem_filter.1 hi
    rw [List.mem_toFinset]
    by_contra hiI
    have : c i = 0 := by
      rw [hc]
      refine List.sum_eq_zero fun z hz => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
      split
      · obtain ⟨-, hsub⟩ := h4 e he
        have := congrArg (fun z => Nat.testBit z i) hsub
        simp only [Nat.testBit_and, testBit_bitsL] at this
        unfold bitZ
        cases hb : (e / 32).testBit i
        · rfl
        · rw [hb, decide_eq_false hiI] at this
          exact absurd this (by decide)
      · rfl
    rw [this] at hci
    exact absurd hci (by decide)
  funext r
  have hrr := r.isLt
  have hq : 32 * (r : ℕ) + j < 384 := by omega
  have hE := beq_true (hrel k hk)
  change rowAt HP (k + 1) &&& (repN * spread 4095 * depBits DEPA) =
    mixK DEPA (rowAt HP (k + 1)) (repN * spread 4095) ^^^
      ((mulRowK (getL [] SP k) BR (repN * 1073741823) ^^^ permF BR LMP (128 * k)) ^^^
        fieldAt BR (k + 1) * repN) at hE
  have eb := congrArg (fun z => bitZ z (384 * t + (32 * r + j))) hE
  rw [bitZ_and_L0dep hdep hjd ht hrr hj, bitZ_xor, bitZ_xor, bitZ_xor,
    bitZ_mixK _ _ ht hrr hj, bitZ'_mulRowK (spyK_spec hsp hSP hk) _ ht hrr hj,
    bitZ_permF _ _ _ ht hq, bitZ_rep _ _ ht hq, (matOfCols_matWordK _).1] at eb
  rw [show pg 7 127 LMP (128 * k + t) = lmul k t from hl k hk t ht] at eb
  simp only [Pi.add_apply, Finset.sum_apply, bv_hv]
  have hs : (matOfCols (yCols k)).mulVec (bv (hvR BR j t)) r = ∑ i ∈ Finset.range 12,
      bitZ ((matWordK aCols bCols (getL [] yWords k)).getD i 0) r * bitZ BR (384 * t + (32 * i + j)) := by
    have hm : matOfCols (matWordK aCols bCols (getL [] yWords k)) = matOfCols (yCols k) := by
      rw [(matOfCols_matWordK _).2, yCols, nth_eq_getD, getL_eq]
    rw [← Fin.sum_univ_eq_sum_range (fun i => bitZ ((matWordK aCols bCols (getL [] yWords k)).getD i 0) r *
        bitZ BR (384 * t + (32 * i + j))), ← hm]
    simp only [Matrix.mulVec, dotProduct, matOfCols, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ * (if (hvR BR j t).testBit i then 1 else 0) = _
    rw [testBit_hvR, decide_eq_true i.isLt, Bool.true_and]
    rfl
  have hbv : ∀ x, bv (hvR BR j x) r = bitZ BR (384 * x + (32 * r + j)) := fun x => by
    change (if (hvR BR j x).testBit r then (1 : ZMod 2) else 0) = _
    rw [testBit_hvR, decide_eq_true hrr, Bool.true_and]
    rfl
  have hA : ∑ i ∈ (Finset.range 30).filter (fun i => c i = 1),
      bitZ (rowAt HP (k + 1)) (384 * t + (32 * r + i)) =
      ∑ i ∈ Finset.range 30, c i * bitZ (rowAt HP (k + 1)) (384 * t + (32 * r + i)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hc01 i with h | h <;> simp [h]
  rw [hs, hbv, hbv, hA, eb]

theorem conj_num {A B : ℕ}
    {E : ℕ → ℕ} {CW CQ : List (List ℕ)} (h : conjK A B E CW CQ = true)
    (hbr : ∀ (w : List ℕ) (x y : ℕ), x < 128 → y < 128 →
      Nat.beq (pcomp 315 9 511 (wordK A B w) (E x)) (pcomp 315 9 511 (E y) (wordK A B w)) = true →
        wordP w * incl (elt x) = incl (elt y) * wordP w) :
    ∀ l < 5, ∀ e ∈ getL [] CQ l, e % 128 < 128 ∧ e / 128 < 128 ∧
      wordP (getL [] CW l) * incl (elt (e % 128)) = incl (elt (e / 128)) * wordP (getL [] CW l) := by
  intro l hl e he
  have h1 := CFSG.KS.PK.allN_iff.1 h l hl
  rw [CFSG.KS.PK.strictB_eq] at h1
  obtain ⟨he1, he2⟩ := conjL_spec h1 e he
  exact ⟨Nat.mod_lt _ (by norm_num), by omega,
    hbr _ _ _ (Nat.mod_lt _ (by norm_num)) (by omega) he2⟩

@[expose] noncomputable def dotL (μ : ℕ) : V12 →ₗ[ZMod 2] ZMod 2 :=
  ∑ r : Fin 12, if μ.testBit r then LinearMap.proj r else 0

@[expose] noncomputable def cellsAt (CQ PHI : List (List ℕ)) (NL : List ℕ) (l m : ℕ) :
    List (↥S × ↥S × ↥S × ↥S × (V12 →ₗ[ZMod 2] ZMod 2)) :=
  (List.range (getL [] CQ l).length).flatMap fun a => (List.range (getL [] CQ l).length).map fun b =>
    ((elt ((getL [] CQ l).getD a 0 % 128), elt ((getL [] CQ l).getD a 0 / 128),
      elt ((getL [] CQ l).getD b 0 % 128), elt ((getL [] CQ l).getD b 0 / 128),
      dotL ((getL 0 (getL [] PHI l) a / 2 ^ (12 * (getL 0 NL l * b + m))) % 4096)))

@[expose] noncomputable def cellSum (n : ℕ) (f : ℕ → ℕ → ZMod 2) : ZMod 2 :=
  ((List.range n).flatMap fun a => (List.range n).map fun b => f a b).sum

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem cellSum_congr {n : ℕ} {f g : ℕ → ℕ → ZMod 2} (h : ∀ a < n, ∀ b < n, f a b = g a b) :
    cellSum n f = cellSum n g := by
  unfold cellSum
  congr 1
  exact flatMap_congr' fun a ha => List.map_congr_left fun b hb =>
    h a (List.mem_range.1 ha) b (List.mem_range.1 hb)

@[expose] noncomputable def muAt (CQ PHI : List (List ℕ)) (NL : List ℕ) (l m a b : ℕ) : ℕ :=
  (getL 0 (getL [] PHI l) a / 2 ^ (12 * (getL 0 NL l * b + m))) % 4096

theorem phiL_cellsAt (CQ PHI : List (List ℕ)) (NL : List ℕ) (l m : ℕ) (F : ↥S → ↥S → V12) :
    phiL (cellsAt CQ PHI NL l m) F = cellSum (getL [] CQ l).length fun a b =>
      dotL (muAt CQ PHI NL l m a b) (F (elt ((getL [] CQ l).getD a 0 % 128))
        (elt ((getL [] CQ l).getD b 0 % 128))) := by
  simp only [phiL, cellsAt, cellSum, muAt, List.map_flatMap, List.map_map, Function.comp_def]

theorem psiL_cellsAt (ρ : ↥P →* Module.End (ZMod 2) V12) (g : ↥P) (CQ PHI : List (List ℕ))
    (NL : List ℕ) (l m : ℕ) (F : ↥S → ↥S → V12) :
    psiL ρ g (cellsAt CQ PHI NL l m) F = cellSum (getL [] CQ l).length fun a b =>
      dotL (muAt CQ PHI NL l m a b) (F (elt ((getL [] CQ l).getD a 0 % 128))
        (elt ((getL [] CQ l).getD b 0 % 128)) - ρ g⁻¹ (F (elt ((getL [] CQ l).getD a 0 / 128))
          (elt ((getL [] CQ l).getD b 0 / 128)))) := by
  simp only [psiL, cellsAt, cellSum, muAt, List.map_flatMap, List.map_map, Function.comp_def]

@[expose] noncomputable def unpackM (R : ℕ) : List ℕ := (List.range 12).map fun c => R / 2 ^ (12 * c) % 4096

theorem unpack_pack_id : matOfCols (unpackM (packM id12)) = 1 := by
  decide +kernel

theorem unpack_pack_Y : ∀ k < 3, unpackM (packM (matWordK aCols bCols (getL [] yWords k))) =
    matWordK aCols bCols (getL [] yWords k) := by
  decide +kernel

theorem fld4095 (Y o : ℕ) : Nat.land (Nat.shiftRight Y o) 4095 = Y / 2 ^ o % 4096 := by
  change (Y >>> o) &&& (2 ^ 12 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem mvP_aux (Y v : ℕ) : ∀ n, bv (Nat.rec (motive := fun _ => Nat) 0
    (fun c ih => Nat.xor ih (Nat.mul fld(v, c, 1) fld(Y, Nat.mul 12 c, 4095))) n : ℕ) =
    ∑ c ∈ Finset.range n, if v.testBit c then bv (Y / 2 ^ (12 * c) % 4096) else 0
  | 0 => by
    change bv 0 = _
    simp [bv_zero]
  | n + 1 => by
    change bv (_ ^^^ _) = _
    rw [bv_xor, mvP_aux Y v n, Finset.sum_range_succ, fld1_eq]
    congr 1
    have e : Nat.land (Nat.shiftRight Y (12 * n)) 4095 = Y / 2 ^ (12 * n) % 4096 := fld4095 Y _
    by_cases hv : v.testBit n = true
    · simp only [hv, if_true, Nat.mul_eq, Nat.one_mul]
      exact congrArg bv e
    · simp [hv, bv_zero]

theorem mvP_lt (Y v : ℕ) : mvP Y v < 4096 := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
      (fun c ih => Nat.xor ih (Nat.mul fld(v, c, 1) fld(Y, Nat.mul 12 c, 4095))) n : ℕ) < 2 ^ 12 := by
    intro n
    induction n with
    | zero => exact Nat.two_pow_pos 12
    | succ n ih =>
      change _ ^^^ _ < 2 ^ 12
      refine Nat.xor_lt_two_pow ih ?_
      rw [fld1_eq, fld4095]
      split
      · rw [Nat.mul_eq, Nat.one_mul]
        exact Nat.mod_lt _ (by norm_num)
      · rw [Nat.mul_eq, Nat.zero_mul]
        exact Nat.two_pow_pos 12
  exact key 12

theorem unpackM_getD (R : ℕ) {c : ℕ} (hc : c < 12) : (unpackM R).getD c 0 = R / 2 ^ (12 * c) % 4096 := by
  rw [unpackM, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

theorem bv_mvP (Y v : ℕ) : bv (mvP Y v) = (matOfCols (unpackM Y)).mulVec (bv v) := by
  have e : bv (mvP Y v) = _ := mvP_aux Y v 12
  rw [e, ← Fin.sum_univ_eq_sum_range
    (fun c : ℕ => if v.testBit c then bv (Y / 2 ^ (12 * c) % 4096) else 0)]
  funext r
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, matOfCols, Matrix.of_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [unpackM_getD Y c.isLt]
  by_cases hv : v.testBit c = true
  · simp [hv, bv]
  · simp [hv, bv]

theorem testBit_mulMP (Y R q : ℕ) : (mulMP Y R).testBit q =
    (decide (q < 144) && (mvP Y (R / 2 ^ (12 * (q / 12)) % 4096)).testBit (q % 12)) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun c ih => Nat.lor ih
      (Nat.shiftLeft (mvP Y fld(R, Nat.mul 12 c, 4095)) (Nat.mul 12 c))) n : ℕ).testBit q =
      (decide (q < 12 * n) && (mvP Y (R / 2 ^ (12 * (q / 12)) % 4096)).testBit (q % 12)) := by
    intro n
    induction n with
    | zero =>
      change (0 : ℕ).testBit q = _
      simp
    | succ n ih =>
      change (_ ||| _ <<< (12 * n) : ℕ).testBit q = _
      rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft, fld4095]
      by_cases h1 : q < 12 * n
      · have h2 : ¬ 12 * n ≤ q := by omega
        have h3 : q < 12 * (n + 1) := by omega
        simp [h1, h2, h3]
      · by_cases h3 : q < 12 * (n + 1)
        · have h4 : q / 12 = n := by omega
          have h5 : q - 12 * n = q % 12 := by omega
          simp [h1, h3, h4, h5, show 12 * n ≤ q by omega]
        · have h6 : (mvP Y (R / 2 ^ (12 * n) % 4096)).testBit (q - 12 * n) = false :=
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (mvP_lt _ _)
              (by rw [show (4096 : ℕ) = 2 ^ 12 by norm_num]
                  exact Nat.pow_le_pow_right (by norm_num) (by omega)))
          simp [h1, h3, h6]
  exact key 12

theorem matOfCols_unpackM_mulMP (Y R : ℕ) :
    matOfCols (unpackM (mulMP Y R)) = matOfCols (unpackM Y) * matOfCols (unpackM R) := by
  ext r c
  have hf : mulMP Y R / 2 ^ (12 * (c : ℕ)) % 4096 = mvP Y (R / 2 ^ (12 * (c : ℕ)) % 4096) := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 12
    · rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, testBit_field _ _ _ _ hi, testBit_mulMP]
      have e1 : (12 * c + i) / 12 = c := by omega
      have e2 : (12 * c + i) % 12 = i := by omega
      have e3 : 12 * (c : ℕ) + i < 144 := by omega
      rw [e1, e2, decide_eq_true e3, Bool.true_and]
      rfl
    · rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, Nat.testBit_mod_two_pow, decide_eq_false hi,
        Bool.false_and]
      exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (mvP_lt _ _)
        (by rw [show (4096 : ℕ) = 2 ^ 12 by norm_num]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
  have e := congrFun (bv_mvP Y (R / 2 ^ (12 * (c : ℕ)) % 4096)) r
  simp only [matOfCols, Matrix.of_apply, Matrix.mul_apply] at e ⊢
  rw [unpackM_getD _ c.isLt, hf, e]
  simp only [Matrix.mulVec, dotProduct, matOfCols, Matrix.of_apply, unpackM_getD _ c.isLt]

theorem rsK_spec {RS : List ℕ} {GP PP LMP : ℕ} (hrs : rsK RS GP PP aCols bCols yWords = true)
    (hd : dataK GP PP LMP genT parT lT = true) :
    matOfCols (unpackM (getL 0 RS 0)) = 1 ∧ ∀ x, x ≠ 0 → x < 128 →
      matOfCols (unpackM (getL 0 RS x)) =
        matOfCols (yCols (gen x)) * matOfCols (unpackM (getL 0 RS (par x))) := by
  obtain ⟨hg, hp, -⟩ := data_spec hd
  change bAnd(Nat.beq (getL 0 RS 0) (packM id12), allN 3 (fun k =>
    strictB (packM (matWordK aCols bCols (getL [] yWords k))) (fun Y => allN 127 (fun i =>
      bIf(Nat.beq (pg 2 3 GP (Nat.succ i)) k,
        Nat.beq (getL 0 RS (Nat.succ i)) (mulMP Y (getL 0 RS (pg 7 127 PP (Nat.succ i)))), true)))))
    = true at hrs
  rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at hrs
  obtain ⟨h0, hk⟩ := hrs
  refine ⟨by rw [beq_true h0]; exact unpack_pack_id, fun x hx0 hx => ?_⟩
  have hk' := CFSG.KS.PK.allN_iff.1 hk (gen x) (gen_lt x)
  rw [CFSG.KS.PK.strictB_eq] at hk'
  have h1 := CFSG.KS.PK.allN_iff.1 hk' (x - 1) (by omega)
  have hx1 : Nat.succ (x - 1) = x := by omega
  rw [CFSG.KS.PK.bIf_eq, hx1, hg x hx, if_pos (Nat.beq_refl _), hp x hx] at h1
  rw [beq_true h1, matOfCols_unpackM_mulMP, unpack_pack_Y (gen x) (gen_lt x),
    (matOfCols_matWordK _).2, yCols, nth_eq_getD, getL_eq]

theorem rhoS_elt {RS : List ℕ} {GP PP LMP : ℕ} (hrs : rsK RS GP PP aCols bCols yWords = true)
    (hd : dataK GP PP LMP genT parT lT = true) {ρ : ↥P →* Module.End (ZMod 2) V12}
    (hρ : IsMRep ρ) : ∀ x < 128, ∀ v : V12,
      rhoS ρ (elt x) v = (matOfCols (unpackM (getL 0 RS x))).mulVec v := by
  obtain ⟨h0, hs⟩ := rsK_spec hrs hd
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx v
    by_cases hx0 : x = 0
    · subst hx0
      rw [elt_zero, map_one, h0, Matrix.one_mulVec, Module.End.one_apply]
    · rw [elt_cons hx0 hx, map_mul, Module.End.mul_apply,
        ih _ (par_lt hx0) ((par_lt hx0).trans hx), rhoS_yS hρ (gen_lt x), Matrix.mulVec_mulVec,
        hs x hx0 hx]

theorem rgK_spec {CW RGI : List (List ℕ)} (hrg : rgK aCols (matMulK bCols bCols) CW RGI = true) :
    ∀ l < 5, matOfCols (getL [] RGI l) = matOfCols (matWordInv (getL [] CW l)) := by
  intro l hl
  rw [lbeq_spec (CFSG.KS.PK.allN_iff.1 hrg l hl)]
  change matOfCols (List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun j _ ih acc => ih (matMulK (Bool.rec (motive := fun _ => List Nat) (matMulK bCols bCols)
        aCols (Nat.beq j 0)) acc)) (getL [] CW l) id12) = _
  rw [matWordInvK_aux, matOfCols_id12, mul_one, matWordInv, matOfCols_matWordInv_aux,
    matOfCols_idCols, mul_one]

theorem bitZ_xorL_aux (f : ℕ → ℕ → ℕ) (q : ℕ) : ∀ (Q : List ℕ) (b0 : ℕ),
    bitZ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun e _ ih b => Nat.xor (f b e) (ih (Nat.succ b))) Q b0 : ℕ) q =
      ∑ a ∈ Finset.range Q.length, bitZ (f (b0 + a) (Q.getD a 0)) q
  | [], _ => by
    change bitZ 0 q = _
    simp [bitZ]
  | e :: Q, b0 => by
    have ih := bitZ_xorL_aux f q Q (b0 + 1)
    have h : ∀ a, b0 + 1 + a = b0 + (a + 1) := fun a => by omega
    simp only [h] at ih
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [← ih]
    change bitZ (f b0 e ^^^ _) q = _
    rw [bitZ_xor, add_comm]

theorem bitZ_xorL (f : ℕ → ℕ → ℕ) (Q : List ℕ) (q : ℕ) :
    bitZ (xorL f Q) q = ∑ a ∈ Finset.range Q.length, bitZ (f a (Q.getD a 0)) q := by
  have := bitZ_xorL_aux f q Q 0
  simp only [Nat.zero_add] at this
  exact this

theorem contrib_lt (μ D : ℕ) : contrib μ D < 2 ^ 30 := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun r ih => Nat.xor ih
      (nIf(Nat.beq fld(μ, r, 1) 1, fld(D, Nat.mul 32 r, 1073741823), 0))) n : ℕ) < 2 ^ 30 := by
    intro n
    induction n with
    | zero => exact Nat.two_pow_pos 30
    | succ n ih =>
      change _ ^^^ _ < 2 ^ 30
      refine Nat.xor_lt_two_pow ih ?_
      rw [CFSG.KS.PK.nIf_eq]
      split
      · change (D >>> (32 * n)) &&& (2 ^ 30 - 1) < 2 ^ 30
        exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
      · exact Nat.two_pow_pos 30
  exact key 12

theorem bitZ_contrib (μ D : ℕ) {i : ℕ} (hi : i < 30) :
    bitZ (contrib μ D) i = ∑ r ∈ Finset.range 12, bitZ μ r * bitZ D (32 * r + i) := by
  have key : ∀ n, bitZ (Nat.rec (motive := fun _ => Nat) 0 (fun r ih => Nat.xor ih
      (nIf(Nat.beq fld(μ, r, 1) 1, fld(D, Nat.mul 32 r, 1073741823), 0))) n) i =
      ∑ r ∈ Finset.range n, bitZ μ r * bitZ D (32 * r + i) := by
    intro n
    induction n with
    | zero =>
      change bitZ 0 i = _
      simp [bitZ]
    | succ n ih =>
      change bitZ (_ ^^^ _) i = _
      rw [bitZ_xor, ih, Finset.sum_range_succ, CFSG.KS.PK.nIf_eq, fld1_eq]
      congr 1
      by_cases hμ : μ.testBit n = true
      · rw [if_pos (by rw [if_pos hμ]; rfl)]
        unfold bitZ
        rw [if_pos hμ, one_mul]
        change (if ((D >>> (32 * n)) &&& 1073741823).testBit i = true then (1 : ZMod 2) else 0) = _
        rw [testBit_mask30, Nat.testBit_shiftRight, decide_eq_true hi, Bool.and_true]
      · rw [if_neg (by rw [if_neg hμ]; decide)]
        unfold bitZ
        rw [if_neg hμ, zero_mul]
        simp
  exact key 12

theorem bitZ_shl32 {X : ℕ} (hX : X < 2 ^ 30) (s F i : ℕ) (hi : i < 30) :
    bitZ (X <<< (32 * s)) (32 * F + i) = if F = s then bitZ X i else 0 := by
  rw [bitZ_shl]
  by_cases hF : F = s
  · subst hF
    rw [if_pos (by omega), if_pos rfl, show 32 * F + i - 32 * F = i by omega]
  · rw [if_neg hF]
    split
    · unfold bitZ
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      simp
    · rfl

theorem bitZ_mulRowK1 {sp : List ℕ} {V : ℕ → ℕ} (hsp : ∀ c < sp.length, sp.getD c 0 = spread (V c))
    (R : ℕ) {r i : ℕ} (hr : r < 12) (hi : i < 30) :
    bitZ (mulRowK sp R 1073741823) (32 * r + i) =
      ∑ c ∈ Finset.range sp.length, bitZ (V c) r * bitZ R (32 * c + i) := by
  have e := bitZ'_mulRowK_aux R 1073741823 (32 * r + i) sp 0
  change bitZ (mulRowK sp R 1073741823) _ = _ at e
  rw [e]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [hsp c (Finset.mem_range.1 hc), Nat.mul_comm, Nat.zero_add]
  have hx : ∀ h, ((R >>> (32 * c)) &&& 1073741823) / 2 ^ (384 * h) % 2 ^ 384 < 2 ^ 30 :=
    fun h => lt_of_le_of_lt (le_trans (Nat.mod_le _ _) (Nat.div_le_self _ _))
      (Nat.and_lt_two_pow _ (by norm_num))
  have hs := testBit_spread_mul (v := V c) hx (h := 0) hr hi
  rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add] at hs
  unfold bitZ
  rw [hs, testBit_mask30, Nat.testBit_shiftRight, decide_eq_true hi, Bool.and_true]
  cases (V c).testBit r <;> cases R.testBit (32 * c + i) <;> simp

theorem bitZ_phiCell (sp : List ℕ) (n o Mu b rowS rowP t pt F : ℕ) {i : ℕ} (hi : i < 30) :
    bitZ (phiCell sp n o Mu b rowS rowP t pt) (32 * F + i) = ∑ m ∈ Finset.range n,
      if F = o + m then bitZ (contrib (Mu / 2 ^ (12 * (n * b + m)) % 4096)
        (Nat.xor (fieldAt rowS t) (mulRowK sp (fieldAt rowP pt) 1073741823))) i else 0 := by
  have key : ∀ k, bitZ (Nat.rec (motive := fun _ => Nat) 0 (fun m ih => Nat.xor ih
      (Nat.shiftLeft (contrib fld(Mu, Nat.mul 12 (Nat.add (Nat.mul n b) m), 4095)
        (Nat.xor (fieldAt rowS t) (mulRowK sp (fieldAt rowP pt) 1073741823))) (Nat.mul 32 (Nat.add o m)))) k)
      (32 * F + i) = ∑ m ∈ Finset.range k,
      if F = o + m then bitZ (contrib (Mu / 2 ^ (12 * (n * b + m)) % 4096)
        (Nat.xor (fieldAt rowS t) (mulRowK sp (fieldAt rowP pt) 1073741823))) i else 0 := by
    intro k
    induction k with
    | zero =>
      change bitZ 0 _ = _
      simp [bitZ]
    | succ k ih =>
      change bitZ (_ ^^^ _ <<< (32 * (o + k))) _ = _
      rw [bitZ_xor, ih, Finset.sum_range_succ, bitZ_shl32 (contrib_lt _ _) _ _ _ hi, fld4095]
      rfl
  exact key n

theorem offL_succ (NL : List ℕ) (l : ℕ) : offL NL (l + 1) = offL NL l + getL 0 NL l := rfl

theorem list_sum_map_range' {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_map_range' f n,
      Finset.sum_range_succ]
    simp

theorem cellSum_eq (n : ℕ) (f : ℕ → ℕ → ZMod 2) :
    cellSum n f = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, f a b := by
  have hf : ∀ (L : List ℕ) (g : ℕ → List (ZMod 2)),
      (L.flatMap g).sum = (L.map fun a => (g a).sum).sum := by
    intro L g
    induction L with
    | nil => rfl
    | cons a L ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]
  unfold cellSum
  rw [hf, ← list_sum_map_range']
  congr 1

theorem bitZ_nxor (x y b : ℕ) : bitZ (Nat.xor x y) b = bitZ x b + bitZ y b := bitZ_xor x y b

theorem dotL_apply (μ : ℕ) (v : V12) : dotL μ v = ∑ r : Fin 12, bitZ μ r * v r := by
  rw [dotL, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold bitZ
  split <;> simp

theorem and127 (e : ℕ) : Nat.land e 127 = e % 128 := Nat.and_two_pow_sub_one_eq_mod e 7

theorem shr7 (e : ℕ) : Nat.shiftRight e 7 = e / 128 := Nat.shiftRight_eq_div_pow e 7

theorem offL_mono (NL : List ℕ) {l l' : ℕ} (h : l ≤ l') : offL NL l ≤ offL NL l' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [offL_succ]; omega)

theorem offL_inj (NL : List ℕ) {l l' m m' : ℕ} (hm : m < getL 0 NL l) (hm' : m' < getL 0 NL l')
    (h : offL NL l + m = offL NL l' + m') : l = l' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := offL_mono NL (Nat.succ_le_of_lt hlt)
    rw [offL_succ] at this
    omega
  · have := offL_mono NL (Nat.succ_le_of_lt hlt)
    rw [offL_succ] at this
    omega

theorem bitZ_phv (HP : ℕ) (CQ PHI SPG : List (List ℕ)) (NL : List ℕ) (q : ℕ) : ∀ n,
    bitZ (Nat.rec (motive := fun _ => Nat) 0
      (fun l ih => Nat.xor ih (phiAcc HP CQ PHI SPG NL l)) n) q =
      ∑ l ∈ Finset.range n, bitZ (phiAcc HP CQ PHI SPG NL l) q
  | 0 => by
    change bitZ 0 q = _
    simp [bitZ]
  | n + 1 => by
    change bitZ (_ ^^^ _) q = _
    rw [bitZ_xor, bitZ_phv HP CQ PHI SPG NL q n, Finset.sum_range_succ]

theorem bitZ_phiAcc (HP : ℕ) (CQ PHI SPG : List (List ℕ)) (NL : List ℕ) (l F : ℕ) {i : ℕ}
    (hi : i < 30) : bitZ (phiAcc HP CQ PHI SPG NL l) (32 * F + i) =
      ∑ a ∈ Finset.range (getL [] CQ l).length, ∑ b ∈ Finset.range (getL [] CQ l).length,
        ∑ m ∈ Finset.range (getL 0 NL l), if F = offL NL l + m then
          bitZ (contrib (getL 0 (getL [] PHI l) a / 2 ^ (12 * (getL 0 NL l * b + m)) % 4096)
            (Nat.xor (fieldAt (rowAt HP ((getL [] CQ l).getD a 0 % 128)) ((getL [] CQ l).getD b 0 % 128))
              (mulRowK (getL [] SPG l) (fieldAt (rowAt HP ((getL [] CQ l).getD a 0 / 128))
                ((getL [] CQ l).getD b 0 / 128)) 1073741823))) i else 0 := by
  unfold phiAcc
  rw [bitZ_xorL]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [CFSG.KS.PK.strictN_eq, CFSG.KS.PK.strictN_eq, bitZ_xorL]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [bitZ_phiCell _ _ _ _ _ _ _ _ _ _ hi]
  simp only [and127, shr7]

theorem psi_num {HP : ℕ} {NL : List ℕ} {CQ PHI SPG RGI : List (List ℕ)} {PHV : ℕ}
    (hpv : phvK HP CQ PHI SPG NL PHV = true) (hspg : spgK RGI SPG = true)
    (hSPG : ∀ l < 5, (getL [] SPG l).length = 12) :
    ∀ l < 5, ∀ m < getL 0 NL l, ∀ i < 30, cellSum (getL [] CQ l).length (fun a b =>
      dotL (muAt CQ PHI NL l m a b)
        (bv (hv HP i ((getL [] CQ l).getD a 0 % 128) ((getL [] CQ l).getD b 0 % 128)) -
          (matOfCols (getL [] RGI l)).mulVec
            (bv (hv HP i ((getL [] CQ l).getD a 0 / 128) ((getL [] CQ l).getD b 0 / 128))))) =
        bitZ PHV (32 * (offL NL l + m) + i) := by
  intro l hl m hm i hi
  have hq : bitZ PHV (32 * (offL NL l + m) + i) = ∑ l' ∈ Finset.range 5,
      bitZ (phiAcc HP CQ PHI SPG NL l') (32 * (offL NL l + m) + i) := by
    rw [← beq_true hpv]
    exact bitZ_phv HP CQ PHI SPG NL _ 5
  rw [hq, Finset.sum_eq_single l (fun l' _ hne => ?_) (fun h => absurd (Finset.mem_range.2 hl) h),
    bitZ_phiAcc _ _ _ _ _ _ _ hi, cellSum_eq]
  · have hsp : ∀ c < (getL [] SPG l).length,
        (getL [] SPG l).getD c 0 = spread ((getL [] RGI l).getD c 0) := fun c hc => by
      have h := CFSG.KS.PK.allN_iff.1 hspg l hl
      have e := beq_true (CFSG.KS.PK.allN_iff.1 h c (by rw [hSPG l hl] at hc; exact hc))
      rwa [getL_eq 0 (getL [] SPG l) c, getL_eq 0 (getL [] RGI l) c] at e
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single m (fun m' _ hne => if_neg (by omega))
      (fun h => absurd (Finset.mem_range.2 hm) h), if_pos rfl, bitZ_contrib _ _ hi, dotL_apply,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hr := r.isLt
    rw [bitZ_nxor, bitZ_fieldAt _ _ _ (by omega), bitZ_mulRowK1 hsp _ hr hi, hSPG l hl,
      Pi.sub_apply, sub_eq_add_neg, neg_eq_self_zmod2, muAt, bv_hv]
    have h2 : (matOfCols (getL [] RGI l)).mulVec
        (bv (hv HP i ((getL [] CQ l).getD a 0 / 128) ((getL [] CQ l).getD b 0 / 128))) r =
        ∑ c ∈ Finset.range 12, bitZ ((getL [] RGI l).getD c 0) r *
          bitZ (fieldAt (rowAt HP ((getL [] CQ l).getD a 0 / 128)) ((getL [] CQ l).getD b 0 / 128))
            (32 * c + i) := by
      simp only [Matrix.mulVec, dotProduct, matOfCols, Matrix.of_apply]
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [bv_hv, bitZ_fieldAt _ _ _ (by omega)]
      rfl
    rw [h2]
  · rw [bitZ_phiAcc _ _ _ _ _ _ _ hi]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun m' hm' => if_neg fun h => hne ?_
    exact (offL_inj NL hm (Finset.mem_range.1 hm') h).symm

theorem psi_sound {HP : ℕ} {NL : List ℕ} {CQ PHI SPG RGI CW : List (List ℕ)} {PHV : ℕ}
    (hpv : phvK HP CQ PHI SPG NL PHV = true) (hspg : spgK RGI SPG = true)
    (hSPG : ∀ l < 5, (getL [] SPG l).length = 12)
    (hrg : rgK aCols (matMulK bCols bCols) CW RGI = true)
    (hb : ∀ l < 5, ∀ e ∈ getL [] CQ l, e / 128 < 128)
    {ρ : ↥P →* Module.End (ZMod 2) V12} (hρ : IsMRep ρ) :
    ∀ l < 5, ∀ m < getL 0 NL l, ∀ i < 30,
      psiL ρ (wordP (getL [] CW l)) (cellsAt CQ PHI NL l m) (Hc HP i) =
        bitZ PHV (32 * (offL NL l + m) + i) := by
  intro l hl m hm i hi
  rw [psiL_cellsAt, ← psi_num hpv hspg hSPG l hl m hm i hi]
  refine cellSum_congr fun a ha b hb' => ?_
  have hpa : (getL [] CQ l).getD a 0 / 128 < 128 :=
    hb l hl _ (by rw [List.getD_eq_getElem _ _ ha]; exact List.getElem_mem ha)
  have hpb : (getL [] CQ l).getD b 0 / 128 < 128 :=
    hb l hl _ (by rw [List.getD_eq_getElem _ _ hb']; exact List.getElem_mem hb')
  rw [Hc_elt HP i (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)), Hc_elt HP i hpa hpb,
    rho_wordP_inv hρ, ← rgK_spec hrg l hl]

theorem bitZ_shl12 {X : ℕ} (hX : X < 2 ^ 12) (G F r : ℕ) (hr : r < 12) :
    bitZ (X <<< (12 * G)) (12 * F + r) = if F = G then bitZ X r else 0 := by
  rw [bitZ_shl]
  by_cases hF : F = G
  · subst hF
    rw [if_pos (by omega), if_pos rfl, show 12 * F + r - 12 * F = r by omega]
  · rw [if_neg hF]
    split
    · unfold bitZ
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      simp
    · rfl

theorem bitZ_par12 (x : ℕ) : bitZ (par12 x) 0 = ∑ r ∈ Finset.range 12, bitZ x r := by
  have h150 : ∀ y < 8, bitZ 150 y = bitZ y 0 + bitZ y 1 + bitZ y 2 := by decide
  have hy : Nat.land (Nat.xor (Nat.xor x (Nat.shiftRight x 6))
      (Nat.shiftRight (Nat.xor x (Nat.shiftRight x 6)) 3)) 7 < 8 :=
    Nat.and_lt_two_pow _ (by norm_num : (7 : ℕ) < 2 ^ 3)
  have hyk : ∀ k < 3, bitZ (Nat.land (Nat.xor (Nat.xor x (Nat.shiftRight x 6))
      (Nat.shiftRight (Nat.xor x (Nat.shiftRight x 6)) 3)) 7) k =
      bitZ x k + bitZ x (6 + k) + (bitZ x (3 + k) + bitZ x (6 + (3 + k))) := by
    intro k hk
    unfold bitZ
    change (if (((x ^^^ x >>> 6) ^^^ (x ^^^ x >>> 6) >>> 3) &&& (2 ^ 3 - 1)).testBit k = true
      then (1 : ZMod 2) else 0) = _
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hk, Bool.and_true,
      Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.add_comm 3 k]
    cases x.testBit k <;> cases x.testBit (6 + k) <;> cases x.testBit (k + 3) <;>
      cases x.testBit (6 + (k + 3)) <;> decide
  have e0 : bitZ (par12 x) 0 = bitZ 150 (Nat.land (Nat.xor (Nat.xor x (Nat.shiftRight x 6))
      (Nat.shiftRight (Nat.xor x (Nat.shiftRight x 6)) 3)) 7) := by
    change bitZ (Nat.land (Nat.shiftRight 150 _) 1) 0 = _
    rw [fld1_eq]
    unfold bitZ
    cases (150 : ℕ).testBit _ <;> rfl
  rw [e0, h150 _ hy, hyk 0 (by norm_num), hyk 1 (by norm_num), hyk 2 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

theorem par12_lt (x : ℕ) : par12 x < 2 := Nat.and_lt_two_pow _ (by norm_num : (1 : ℕ) < 2 ^ 1)

theorem testBit_rT (R μ c : ℕ) : (rT R μ).testBit c =
    (decide (c < 12) && (par12 (Nat.land (R / 2 ^ (12 * c) % 4096) μ)).testBit 0) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun r ih => Nat.lor ih
      (Nat.shiftLeft (par12 (Nat.land fld(R, Nat.mul 12 r, 4095) μ)) r)) n : ℕ).testBit c =
      (decide (c < n) && (par12 (Nat.land (R / 2 ^ (12 * c) % 4096) μ)).testBit 0) := by
    intro n
    induction n with
    | zero =>
      change (0 : ℕ).testBit c = _
      simp
    | succ n ih =>
      change (_ ||| _ <<< n : ℕ).testBit c = _
      rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft, fld4095]
      by_cases h1 : c < n
      · have h2 : ¬ n ≤ c := by omega
        have h3 : c < n + 1 := by omega
        simp [h1, h2, h3]
      · by_cases h3 : c = n
        · subst h3
          simp
        · have h4 : (par12 ((R / 2 ^ (12 * n) % 4096) &&& μ)).testBit (c - n) = false :=
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (par12_lt _)
              (by rw [show (2 : ℕ) = 2 ^ 1 from rfl]; exact Nat.pow_le_pow_right (by norm_num) (by omega)))
          have h5 : ¬ c < n + 1 := by omega
          simp [h1, h5, h4]
  exact key 12

theorem rT_lt (R μ : ℕ) : rT R μ < 2 ^ 12 := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  rw [testBit_rT, decide_eq_false (by omega), Bool.false_and]

theorem bitZ_rT (R μ : ℕ) {c : ℕ} (hc : c < 12) :
    bitZ (rT R μ) c = ∑ r ∈ Finset.range 12, bitZ (R / 2 ^ (12 * c) % 4096) r * bitZ μ r := by
  have e : bitZ (rT R μ) c = bitZ (par12 (Nat.land (R / 2 ^ (12 * c) % 4096) μ)) 0 := by
    unfold bitZ
    rw [testBit_rT, decide_eq_true hc, Bool.true_and]
  rw [e, bitZ_par12]
  refine Finset.sum_congr rfl fun r _ => ?_
  change bitZ ((R / 2 ^ (12 * c) % 4096) &&& μ) r = _
  unfold bitZ
  rw [Nat.testBit_and]
  cases (R / 2 ^ (12 * c) % 4096).testBit r <;> cases μ.testBit r <;> simp

theorem mu_lt (Mu x : ℕ) : Mu / 2 ^ x % 4096 < 2 ^ 12 := Nat.mod_lt _ (by norm_num)

theorem bitZ_uCell (MTP n o Mu b s R t F : ℕ) {r : ℕ} (hr : r < 12) :
    bitZ (uCell MTP n o Mu b s R t) (12 * F + r) = ∑ m ∈ Finset.range n,
      ((if F = 128 * (o + m) + t then bitZ (rT R (Mu / 2 ^ (12 * (n * b + m)) % 4096)) r else 0) +
        ((if F = 128 * (o + m) + pg 7 127 MTP (128 * s + t) then
          bitZ (Mu / 2 ^ (12 * (n * b + m)) % 4096) r else 0) +
        (if F = 128 * (o + m) + s then bitZ (Mu / 2 ^ (12 * (n * b + m)) % 4096) r else 0))) := by
  have key : ∀ k, bitZ (Nat.rec (motive := fun _ => Nat) 0 (fun m ih =>
      (fun μ q0 => Nat.xor ih (Nat.xor (Nat.shiftLeft (rT R μ) (Nat.mul 12 (Nat.add q0 t)))
        (Nat.xor (Nat.shiftLeft μ (Nat.mul 12 (Nat.add q0 (pg 7 127 MTP (Nat.add (Nat.mul 128 s) t)))))
          (Nat.shiftLeft μ (Nat.mul 12 (Nat.add q0 s))))))
      fld(Mu, Nat.mul 12 (Nat.add (Nat.mul n b) m), 4095) (Nat.mul 128 (Nat.add o m))) k)
      (12 * F + r) = ∑ m ∈ Finset.range k,
      ((if F = 128 * (o + m) + t then bitZ (rT R (Mu / 2 ^ (12 * (n * b + m)) % 4096)) r else 0) +
        ((if F = 128 * (o + m) + pg 7 127 MTP (128 * s + t) then
          bitZ (Mu / 2 ^ (12 * (n * b + m)) % 4096) r else 0) +
        (if F = 128 * (o + m) + s then bitZ (Mu / 2 ^ (12 * (n * b + m)) % 4096) r else 0))) := by
    intro k
    induction k with
    | zero =>
      change bitZ 0 _ = _
      simp [bitZ]
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      change bitZ (_ ^^^ ((rT R (Nat.land (Nat.shiftRight Mu (12 * (n * b + k))) 4095) <<<
        (12 * (128 * (o + k) + t))) ^^^
        ((Nat.land (Nat.shiftRight Mu (12 * (n * b + k))) 4095 <<<
          (12 * (128 * (o + k) + pg 7 127 MTP (128 * s + t)))) ^^^
          (Nat.land (Nat.shiftRight Mu (12 * (n * b + k))) 4095 <<< (12 * (128 * (o + k) + s)))))) _ = _
      rw [fld4095, bitZ_xor, bitZ_xor, bitZ_xor, bitZ_shl12 (rT_lt _ _) _ _ _ hr,
        bitZ_shl12 (mu_lt _ _) _ _ _ hr, bitZ_shl12 (mu_lt _ _) _ _ _ hr]
  exact key n

theorem bitZ_uAcc (MTP : ℕ) (RS : List ℕ) (CQ PHI : List (List ℕ)) (NL : List ℕ) (l F : ℕ) {r : ℕ}
    (hr : r < 12) : bitZ (uAcc MTP RS CQ PHI NL l) (12 * F + r) =
      ∑ a ∈ Finset.range (getL [] CQ l).length, ∑ b ∈ Finset.range (getL [] CQ l).length,
        bitZ (uCell MTP (getL 0 NL l) (offL NL l) (getL 0 (getL [] PHI l) a) b
          ((getL [] CQ l).getD a 0 % 128) (getL 0 RS ((getL [] CQ l).getD a 0 % 128))
          ((getL [] CQ l).getD b 0 % 128)) (12 * F + r) := by
  unfold uAcc
  rw [bitZ_xorL]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [CFSG.KS.PK.strictN_eq]
  rw [bitZ_xorL]
  simp only [and127]

theorem phi_num {MTP GP PP LMP : ℕ} {RS NL : List ℕ} {CQ PHI : List (List ℕ)}
    (hphi : ∀ l < 5, phiK MTP RS CQ PHI NL l = true) (hd : dataK GP PP LMP genT parT lT = true)
    (hmt : mtK MTP LMP GP PP = true) :
    ∀ l < 5, ∀ m < getL 0 NL l, ∀ β : ℕ → V12, cellSum (getL [] CQ l).length (fun a b =>
      dotL (muAt CQ PHI NL l m a b)
        ((matOfCols (unpackM (getL 0 RS ((getL [] CQ l).getD a 0 % 128)))).mulVec
            (β ((getL [] CQ l).getD b 0 % 128)) -
          β (mulIdx ((getL [] CQ l).getD a 0 % 128) ((getL [] CQ l).getD b 0 % 128)) +
          β ((getL [] CQ l).getD a 0 % 128))) = 0 := by
  intro l hl m hm β
  have hU : uAcc MTP RS CQ PHI NL l = 0 := beq_true (hphi l hl)
  have hcell : ∀ a b, dotL (muAt CQ PHI NL l m a b)
      ((matOfCols (unpackM (getL 0 RS ((getL [] CQ l).getD a 0 % 128)))).mulVec
          (β ((getL [] CQ l).getD b 0 % 128)) -
        β (mulIdx ((getL [] CQ l).getD a 0 % 128) ((getL [] CQ l).getD b 0 % 128)) +
        β ((getL [] CQ l).getD a 0 % 128)) =
      ∑ q ∈ Finset.range 128, ∑ r : Fin 12, β q r *
        bitZ (uCell MTP (getL 0 NL l) (offL NL l) (getL 0 (getL [] PHI l) a) b
          ((getL [] CQ l).getD a 0 % 128) (getL 0 RS ((getL [] CQ l).getD a 0 % 128))
          ((getL [] CQ l).getD b 0 % 128)) (12 * (128 * (offL NL l + m) + q) + r) := by
    intro a b
    set s := (getL [] CQ l).getD a 0 % 128 with hs
    set t := (getL [] CQ l).getD b 0 % 128 with ht
    have hs' : s < 128 := Nat.mod_lt _ (by norm_num)
    have ht' : t < 128 := Nat.mod_lt _ (by norm_num)
    set R := getL 0 RS s
    set μ := getL 0 (getL [] PHI l) a / 2 ^ (12 * (getL 0 NL l * b + m)) % 4096 with hμ
    have hmt' : pg 7 127 MTP (128 * s + t) = mulIdx s t := mt_spec hmt hd s hs' t ht'
    have hst : mulIdx s t < 128 := (mulIdx_spec ht').1
    have hin : ∀ q < 128, ∀ r : Fin 12, bitZ (uCell MTP (getL 0 NL l) (offL NL l)
        (getL 0 (getL [] PHI l) a) b s R t) (12 * (128 * (offL NL l + m) + q) + r) =
        (if q = t then bitZ (rT R μ) r else 0) + ((if q = mulIdx s t then bitZ μ r else 0) +
          (if q = s then bitZ μ r else 0)) := by
      intro q hq r
      rw [bitZ_uCell _ _ _ _ _ _ _ _ _ r.isLt, Finset.sum_eq_single m, hmt']
      · simp only [Nat.add_left_cancel_iff, hμ]
      · intro m' _ hne
        have h1 : ¬ 128 * (offL NL l + m) + q = 128 * (offL NL l + m') + t := by omega
        have h2 : ¬ 128 * (offL NL l + m) + q = 128 * (offL NL l + m') + pg 7 127 MTP (128 * s + t) := by
          rw [hmt']; omega
        have h3 : ¬ 128 * (offL NL l + m) + q = 128 * (offL NL l + m') + s := by omega
        rw [if_neg h1, if_neg h2, if_neg h3, add_zero, add_zero]
      · intro h
        exact absurd (Finset.mem_range.2 hm) h
    have hR : ∑ q ∈ Finset.range 128, ∑ r : Fin 12, β q r *
        ((if q = t then bitZ (rT R μ) r else 0) + ((if q = mulIdx s t then bitZ μ r else 0) +
          (if q = s then bitZ μ r else 0))) = ∑ r : Fin 12, (β t r * bitZ (rT R μ) r +
            (β (mulIdx s t) r * bitZ μ r + β s r * bitZ μ r)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_range, if_pos ht', if_pos hst, if_pos hs']
    have hM : ∑ r : Fin 12, bitZ μ r * ((matOfCols (unpackM R)).mulVec (β t)) r =
        ∑ r : Fin 12, β t r * bitZ (rT R μ) r := by
      simp only [Matrix.mulVec, dotProduct, matOfCols, Matrix.of_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [bitZ_rT _ _ c.isLt, ← Fin.sum_univ_eq_sum_range
        (fun r => bitZ (R / 2 ^ (12 * (c : ℕ)) % 4096) r * bitZ μ r), Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [unpackM_getD _ c.isLt]
      change bitZ μ r * (bitZ (R / 2 ^ (12 * (c : ℕ)) % 4096) r * β t c) =
        β t c * (bitZ (R / 2 ^ (12 * (c : ℕ)) % 4096) r * bitZ μ r)
      ring
    have hL : ∀ r : Fin 12, bitZ (muAt CQ PHI NL l m a b) r *
        ((matOfCols (unpackM R)).mulVec (β t) - β (mulIdx s t) + β s) r =
        bitZ μ r * ((matOfCols (unpackM R)).mulVec (β t)) r +
          (β (mulIdx s t) r * bitZ μ r + β s r * bitZ μ r) := fun r => by
      simp only [Pi.add_apply, Pi.sub_apply, muAt]
      rw [sub_eq_add_neg, neg_eq_self_zmod2]
      ring
    rw [Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun r _ => by
      rw [hin q (Finset.mem_range.1 hq) r], hR, dotL_apply, Finset.sum_congr rfl fun r _ => hL r,
      Finset.sum_add_distrib, hM, ← Finset.sum_add_distrib]
  have h0 : ∑ q ∈ Finset.range 128, ∑ r : Fin 12, β q r *
      bitZ (uAcc MTP RS CQ PHI NL l) (12 * (128 * (offL NL l + m) + q) + r) = 0 := by
    rw [hU]
    simp [bitZ]
  rw [← h0, cellSum_eq, Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hcell a b]
  simp only [bitZ_uAcc _ _ _ _ _ _ _ (Fin.isLt _), Finset.mul_sum]
  have hre : ∀ (F : ℕ → ℕ → ℕ → Fin 12 → ZMod 2) (A : Finset ℕ),
      ∑ a ∈ A, ∑ b ∈ A, ∑ q ∈ Finset.range 128, ∑ r : Fin 12, F a b q r =
        ∑ q ∈ Finset.range 128, ∑ r : Fin 12, ∑ a ∈ A, ∑ b ∈ A, F a b q r := by
    intro F A
    calc ∑ a ∈ A, ∑ b ∈ A, ∑ q ∈ Finset.range 128, ∑ r : Fin 12, F a b q r
        = ∑ a ∈ A, ∑ q ∈ Finset.range 128, ∑ b ∈ A, ∑ r : Fin 12, F a b q r :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ q ∈ Finset.range 128, ∑ a ∈ A, ∑ b ∈ A, ∑ r : Fin 12, F a b q r := Finset.sum_comm
      _ = ∑ q ∈ Finset.range 128, ∑ a ∈ A, ∑ r : Fin 12, ∑ b ∈ A, F a b q r :=
          Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ q ∈ Finset.range 128, ∑ r : Fin 12, ∑ a ∈ A, ∑ b ∈ A, F a b q r :=
          Finset.sum_congr rfl fun q _ => Finset.sum_comm
  exact hre _ _

theorem phi_sound {MTP GP PP LMP : ℕ} {RS NL : List ℕ} {CQ PHI : List (List ℕ)}
    (hphi : ∀ l < 5, phiK MTP RS CQ PHI NL l = true)
    (hrs : rsK RS GP PP aCols bCols yWords = true) (hd : dataK GP PP LMP genT parT lT = true)
    (hmt : mtK MTP LMP GP PP = true) {ρ : ↥P →* Module.End (ZMod 2) V12} (hρ : IsMRep ρ) :
    ∀ l < 5, ∀ m < getL 0 NL l, ∀ β : ↥S → V12, phiL (cellsAt CQ PHI NL l m) (cob (rhoS ρ) β) = 0 := by
  intro l hl m hm β
  rw [phiL_cellsAt, ← phi_num hphi hd hmt l hl m hm (fun x => β (elt x))]
  refine cellSum_congr fun a _ b _ => ?_
  have hs := Nat.mod_lt ((getL [] CQ l).getD a 0) (by norm_num : 128 > 0)
  have ht := Nat.mod_lt ((getL [] CQ l).getD b 0) (by norm_num : 128 > 0)
  rw [CFSG.RankThree.PartTwo.J2Residue.H2.cob, rhoS_elt hrs hd hρ _ hs, ← (mulIdx_spec ht).2]

theorem rank_num {PHV : ℕ} {IND RINV : List ℕ} (h : rankK PHV IND RINV = true)
    (hI : ∀ i ∈ IND, i < 30) : ∀ ε : ℕ → ZMod 2, (∀ i, i ∉ IND.toFinset → ε i = 0) →
      (∀ m < 10, ∑ i ∈ Finset.range 30, ε i * bitZ PHV (32 * m + i) = 0) →
      ∀ i ∈ IND.toFinset, ε i = 0 := by
  intro ε hε hz i hi
  change bAnd(Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) IND) 10,
    allN 10 (fun i => Nat.beq (Nat.land (selX (getL 0 RINV i) PHV) (bitsL IND))
      (Nat.shiftLeft 1 (getL 0 IND i)))) = true at h
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff] at h
  obtain ⟨hlen, hrow⟩ := h
  have hl : IND.length = 10 := by
    rw [← listLen_eq]
    exact beq_true hlen
  have hiI : i ∈ IND := List.mem_toFinset.1 hi
  obtain ⟨a, ha, hai⟩ := List.mem_iff_getElem.1 hiI
  have hr := beq_true (hrow a (hl ▸ ha))
  rw [getL_eq, getL_eq, List.getD_eq_getElem _ _ ha, hai] at hr
  set R := RINV.getD a 0
  have hpt : ∀ b < 30, ε b * bitZ (selX R PHV) b = if b = i then ε b else 0 := by
    intro b hb
    have e := congrArg (fun z => Nat.testBit z b) hr
    change ((selX R PHV) &&& bitsL IND).testBit b = (1 <<< i).testBit b at e
    rw [Nat.testBit_and, testBit_bitsL, Nat.one_shiftLeft, Nat.testBit_two_pow] at e
    by_cases hbI : b ∈ IND
    · simp only [hbI, decide_true, Bool.and_true] at e
      simp only [bitZ, e, decide_eq_true_eq]
      by_cases hbi : b = i
      · subst hbi
        simp
      · simp [hbi, Ne.symm hbi]
    · have hb0 : ε b = 0 := hε b (by simpa using hbI)
      have hbi : b ≠ i := fun h => hbI (h ▸ hiI)
      simp [hb0, hbi]
  have hsum : ∑ m ∈ Finset.range 10, bitZ R m *
      ∑ b ∈ Finset.range 30, ε b * bitZ PHV (32 * m + b) = 0 :=
    Finset.sum_eq_zero fun m hm => by rw [hz m (Finset.mem_range.1 hm), mul_zero]
  have hsw : ∑ m ∈ Finset.range 10, bitZ R m *
      ∑ b ∈ Finset.range 30, ε b * bitZ PHV (32 * m + b) =
      ∑ b ∈ Finset.range 30, ε b * bitZ (selX R PHV) b := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [bitZ_selX R PHV (Finset.mem_range.1 hb), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hsw, Finset.sum_congr rfl fun b hb => hpt b (Finset.mem_range.1 hb)] at hsum
  simpa [hI i hiI] using hsum

@[expose] noncomputable def formVal (u : ℕ → ZMod 2) (m r : ℕ) : ZMod 2 :=
  ∑ β ∈ Finset.range 4608, if m.testBit (12 * β + r) then u β else 0

@[expose] noncomputable def evalV (u : ℕ → ZMod 2) (m : ℕ) : V12 := fun r => formVal u m r

theorem evalV_xor (u : ℕ → ZMod 2) (a b : ℕ) : evalV u (Nat.xor a b) = evalV u a + evalV u b := by
  funext r
  change formVal u (a ^^^ b) r = formVal u a r + formVal u b r
  rw [formVal, formVal, formVal, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit (12 * q + r) <;> cases b.testBit (12 * q + r) <;> simp [CharTwo.add_self_eq_zero]

theorem evalV_zero (u : ℕ → ZMod 2) : evalV u 0 = 0 := by
  funext r
  simp [evalV, formVal]

theorem evalV_unitF (u : ℕ → ZMod 2) {k x : ℕ} (hk : k < 3) (hx : x < 128) :
    evalV u (unitF k x) = fun r : Fin 12 => u (12 * (128 * k + x) + r) := by
  funext r
  change ∑ β ∈ Finset.range 4608, (if (unitF k x).testBit (12 * β + r) then u β else 0) = _
  simp only [testBit_unitF r.isLt, decide_eq_true_eq]
  rw [Finset.sum_ite_eq']
  have : 12 * (128 * k + x) + (r : ℕ) ∈ Finset.range 4608 := Finset.mem_range.2 (by omega)
  rw [if_pos this]

theorem initK_spec {GP PP LMP : ℕ} (hd : dataK GP PP LMP genT parT lT = true) :
    ∀ β < 4608, (initK GP PP h2Free).testBit (12 * β) = true →
      (∃ x, x ≠ 0 ∧ x < 128 ∧ ∃ r < 12, β = 12 * (128 * gen x + par x) + r) ∨
        ∃ i < 30, β = h2Free.getD i 0 := by
  obtain ⟨hg, hp, -⟩ := data_spec hd
  intro β _ h
  change (_ ||| _ : ℕ).testBit (12 * β) = true at h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨i, hi, r, hr, e⟩ := testBit_treeBits GP PP _ 127 h
    rw [hg _ (by omega), hp _ (by omega)] at e
    exact Or.inl ⟨i + 1, by omega, by omega, r, hr, by omega⟩
  · rw [testBit_bitsF] at h
    obtain ⟨f, hf, e⟩ := of_decide_eq_true h
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hf
    have hl : h2Free.length = 30 := by decide
    exact Or.inr ⟨i, hl ▸ hi, by rw [List.getD_eq_getElem _ _ hi]; omega⟩

theorem ksK_parts {GP PP : ℕ} {KS : List ℕ} {ST : List (List (List ℕ))} {YC : List (List ℕ)}
    (hks : ksK GP PP h2Free KS ST YC aCols bCols yWords = true) :
    getL 0 KS 0 = initK GP PP h2Free ∧ getL 0 KS 6 = oN ∧ ST.length = 6 ∧
      ∀ k < 3, getL [] YC k = matWordK aCols bCols (getL [] yWords k) := by
  change bAnd(Nat.beq (getL 0 KS 0) (initK GP PP h2Free), bAnd(Nat.beq (getL 0 KS 6) oN,
    bAnd(Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) ST) 6,
      allN 3 (fun k => lbeq (getL [] YC k) (matWordK aCols bCols (getL [] yWords k)))))) = true at hks
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff] at hks
  obtain ⟨h1, h2, h3, h4⟩ := hks
  refine ⟨beq_true h1, beq_true h2, ?_, fun k hk => lbeq_spec (h4 k hk)⟩
  rw [← listLen_eq]
  exact beq_true h3

@[expose] noncomputable def gOnes : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ 12 * gOnes n + 1

theorem gOnes_mul (n : ℕ) : gOnes n * 4095 + 1 = 2 ^ (12 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : 2 ^ (12 * (n + 1)) = 2 ^ 12 * 2 ^ (12 * n) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [gOnes, e, ← ih]
    ring

theorem testBit_gOnes (n : ℕ) : ∀ b, (gOnes n).testBit b = decide (b % 12 = 0 ∧ b < 12 * n) := by
  induction n with
  | zero => intro b; simp [gOnes]
  | succ n ih =>
    intro b
    rw [gOnes, Nat.testBit_two_pow_mul_add _ (by norm_num : 1 < 2 ^ 12)]
    split
    · rw [testBit_one', Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      omega
    · rw [ih, Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      omega

theorem oN_eq : oN = gOnes 4608 := by
  change ((1 <<< 55296) - 1) / 4095 = _
  rw [Nat.one_shiftLeft, ← gOnes_mul 4608, Nat.add_sub_cancel, Nat.mul_div_cancel _ (by norm_num)]

theorem testBit_oN {β : ℕ} (hβ : β < 4608) : oN.testBit (12 * β) = true := by
  rw [oN_eq, testBit_gOnes]
  exact decide_eq_true ⟨by omega, by omega⟩

theorem formVal_xor (u : ℕ → ZMod 2) (a b r : ℕ) :
    formVal u (Nat.xor a b) r = formVal u a r + formVal u b r := by
  change formVal u (a ^^^ b) r = formVal u a r + formVal u b r
  rw [formVal, formVal, formVal, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit (12 * q + r) <;> cases b.testBit (12 * q + r) <;> simp [CharTwo.add_self_eq_zero]

theorem formVal_zero (u : ℕ → ZMod 2) (r : ℕ) : formVal u 0 r = 0 := by
  simp [formVal]

theorem field_maskO (v c γ : ℕ) :
    ((v >>> c) &&& oN) / 2 ^ (12 * γ) % 2 ^ 12 =
      if ((v >>> c) &&& oN).testBit (12 * γ) then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · rw [testBit_field _ _ _ _ hi]
    by_cases hi0 : i = 0
    · subst hi0
      rw [Nat.add_zero]
      cases ((v >>> c) &&& oN).testBit (12 * γ) <;> simp
    · have : ((v >>> c) &&& oN).testBit (12 * γ + i) = false := by
        rw [Nat.testBit_and, oN_eq, testBit_gOnes]
        have : ¬ ((12 * γ + i) % 12 = 0 ∧ 12 * γ + i < 12 * 4608) := by omega
        rw [decide_eq_false this, Bool.and_false]
      rw [this]
      cases ((v >>> c) &&& oN).testBit (12 * γ) <;> simp [testBit_one', hi0]
  · rw [Nat.testBit_mod_two_pow]
    have : (if ((v >>> c) &&& oN).testBit (12 * γ) = true then 1 else 0 : ℕ).testBit i = false := by
      split <;> simp [testBit_one']
      omega
    rw [decide_eq_false hi, Bool.false_and, this]

theorem formVal_colMul (u : ℕ → ZMod 2) {col : ℕ} (hcol : col < 4096) (v c : ℕ) {r : ℕ}
    (hr : r < 12) :
    formVal u (col * ((v >>> c) &&& oN)) r = if col.testBit r then formVal u v c else 0 := by
  have hb : ∀ γ, ((v >>> c) &&& oN) / 2 ^ (12 * γ) % 2 ^ 12 * col < 2 ^ 12 := fun γ => by
    rw [field_maskO]
    split
    · rw [Nat.one_mul]
      exact hcol
    · rw [Nat.zero_mul]
      exact Nat.two_pow_pos _
  have hbit : ∀ β < 4608, (col * ((v >>> c) &&& oN)).testBit (12 * β + r) =
      (v.testBit (12 * β + c) && col.testBit r) := by
    intro β hβ
    rw [Nat.mul_comm, ← testBit_field _ _ _ _ hr, fieldMul 12 β _ col hb, field_maskO,
      Nat.testBit_and, Nat.testBit_shiftRight, testBit_oN hβ, Bool.and_true, Nat.add_comm c]
    cases v.testBit (12 * β + c) <;> simp
  unfold formVal
  by_cases hc : col.testBit r = true
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [hbit β (Finset.mem_range.1 hβ), hc, Bool.and_true]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun β hβ => ?_
    rw [hbit β (Finset.mem_range.1 hβ)]
    simp [hc]

theorem formVal_mvI_aux (u : ℕ → ZMod 2) (v : ℕ) {r : ℕ} (hr : r < 12) :
    ∀ (cs : List ℕ) (c : ℕ), (∀ i, cs.getD i 0 < 4096) →
    formVal u (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun col _ ih c => Nat.xor (Nat.mul col (Nat.land (Nat.shiftRight v c) oN)) (ih (Nat.succ c)))
      cs c) r = ∑ i ∈ Finset.range cs.length,
        if (cs.getD i 0).testBit r then formVal u v (c + i) else 0
  | [], _, _ => formVal_zero u r
  | col :: cs, c, hcs => by
    have ih := formVal_mvI_aux u v hr cs (c + 1) fun i => by
      have := hcs (i + 1)
      rwa [List.getD_cons_succ] at this
    have e : ∀ i, c + 1 + i = c + (i + 1) := fun i => by omega
    simp only [e] at ih
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [← ih]
    change formVal u (Nat.xor (col * ((v >>> c) &&& oN)) _) r = _
    have h0 := hcs 0
    rw [List.getD_cons_zero] at h0
    rw [formVal_xor, formVal_colMul u h0 v c hr, add_comm]

theorem matWordK_lt : ∀ k < 3, ∀ i, (matWordK aCols bCols (getL [] yWords k)).getD i 0 < 4096 := by
  have h : ∀ k < 3, ∀ i < 12, (matWordK aCols bCols (getL [] yWords k)).getD i 0 < 4096 := by
    decide +kernel
  intro k hk i
  by_cases hi : i < 12
  · exact h k hk i hi
  · rw [List.getD_eq_default _ _ (by rw [(matOfCols_matWordK _).1]; omega)]
    norm_num

theorem evalV_mvI {GP PP : ℕ} {KS : List ℕ} {ST : List (List (List ℕ))} {YC : List (List ℕ)}
    (hks : ksK GP PP h2Free KS ST YC aCols bCols yWords = true) (u : ℕ → ZMod 2) {k : ℕ}
    (hk : k < 3) (v : ℕ) :
    evalV u (mvI (getL [] YC k) v oN) = (matOfCols (yCols k)).mulVec (evalV u v) := by
  obtain ⟨-, -, -, hY⟩ := ksK_parts hks
  funext r
  have e := formVal_mvI_aux u v r.isLt (getL [] YC k) 0 (by rw [hY k hk]; exact matWordK_lt k hk)
  have e' : formVal u (mvI (getL [] YC k) v oN) r = _ := e
  change formVal u (mvI (getL [] YC k) v oN) r = _
  rw [e', hY k hk, (matOfCols_matWordK _).1, ← Fin.sum_univ_eq_sum_range]
  have hm : matOfCols (yCols k) = matOfCols (matWordK aCols bCols (getL [] yWords k)) := by
    rw [(matOfCols_matWordK _).2, yCols, nth_eq_getD, getL_eq]
  rw [hm]
  simp only [Matrix.mulVec, dotProduct, matOfCols, Matrix.of_apply, bv, Nat.zero_add, evalV]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem formVal_shift (u : ℕ → ZMod 2) (x s : ℕ) :
    formVal u (Nat.land (Nat.shiftRight x s) oN) 0 = formVal u x s := by
  unfold formVal
  refine Finset.sum_congr rfl fun β hβ => ?_
  change (if ((x >>> s) &&& oN).testBit (12 * β + 0) then u β else 0) = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_zero, testBit_oN (Finset.mem_range.1 hβ),
    Bool.and_true, Nat.add_comm s]

theorem maskL_spec {YC : List (List ℕ)} {MTP LMP GP PP O : ℕ} :
    ∀ {cs ms : List ℕ}, maskL YC MTP LMP GP PP O cs ms = true →
      ∀ a, (∃ c, c < 49152 ∧ ms.getD a 0 = cellK YC MTP LMP GP PP O c) ∨ ms.getD a 0 = 0
  | [], [], _ => fun _ => Or.inr rfl
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | c :: cs, m :: ms, h => by
    change bAnd(Nat.blt c 49152, bAnd(Nat.beq m (cellK YC MTP LMP GP PP O c),
      maskL YC MTP LMP GP PP O cs ms)) = true at h
    simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    intro a
    cases a with
    | zero => exact Or.inl ⟨c, h1, beq_true h2⟩
    | succ a =>
      rw [List.getD_cons_succ]
      exact maskL_spec h3 a

theorem formVal_maskAt {YC CKB MB : List (List ℕ)} {MTP LMP GP PP : ℕ} {u : ℕ → ZMod 2}
    (hm : ∀ j < 16, maskBlk YC MTP LMP GP PP CKB MB j = true)
    (hc : ∀ c < 49152, ∀ r < 12, formVal u (cellK YC MTP LMP GP PP oN c) r = 0)
    (hMB : MB.length = 16) : ∀ i r, r < 12 → formVal u (maskAt MB i) r = 0 := by
  intro i r hr
  change formVal u (getL 0 (getL [] MB (i / 32)) (i % 32)) r = 0
  by_cases hj : i / 32 < 16
  · have h := hm _ hj
    change strictB oN (fun O => maskL YC MTP LMP GP PP O (getL [] CKB (i / 32))
      (getL [] MB (i / 32))) = true at h
    rw [CFSG.KS.PK.strictB_eq] at h
    rw [getL_eq 0]
    rcases maskL_spec h (i % 32) with ⟨c, hc', e⟩ | e
    · rw [e]
      exact hc c hc' r hr
    · rw [e]
      exact formVal_zero u r
  · rw [getL_eq [] MB, List.getD_eq_default _ _ (by omega), getL_eq 0, List.getD_nil]
    exact formVal_zero u r

theorem formVal_sumRefs {MB : List (List ℕ)} {u : ℕ → ZMod 2}
    (hmask : ∀ i r, r < 12 → formVal u (maskAt MB i) r = 0) :
    ∀ refs : List ℕ, formVal u (sumRefs MB oN refs) 0 = 0
  | [] => formVal_zero u 0
  | q :: refs => by
    change formVal u (Nat.xor (Nat.land (Nat.shiftRight (maskAt MB (q / 12)) (q % 12)) oN)
      (sumRefs MB oN refs)) 0 = 0
    rw [formVal_xor, formVal_shift, hmask _ _ (Nat.mod_lt _ (by norm_num)),
      formVal_sumRefs hmask refs, add_zero]

theorem add_eq_xor_of_and : ∀ x y : ℕ, x &&& y = 0 → x + y = x ^^^ y := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro y h
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have h2 : x / 2 &&& y / 2 = 0 := by rw [← Nat.and_div_two, h]
      have hm : x % 2 &&& y % 2 = 0 := by
        have := congrArg (· % 2 ^ 1) h
        simp only [Nat.and_mod_two_pow, Nat.zero_mod] at this
        simpa using this
      have e1 := ih (x / 2) (Nat.div_lt_self hx (by norm_num)) (y / 2) h2
      have ex : x ^^^ y = 2 * ((x ^^^ y) / 2) + (x ^^^ y) % 2 := (Nat.div_add_mod _ 2).symm
      have hxm : (x ^^^ y) % 2 = x % 2 + y % 2 := by
        have e2 := Nat.xor_mod_two_pow (a := x) (b := y) (n := 1)
        simp only [pow_one] at e2
        rw [e2]
        rcases Nat.mod_two_eq_zero_or_one x with a | a <;>
          rcases Nat.mod_two_eq_zero_or_one y with b | b <;> rw [a, b] at hm ⊢
        · rfl
        · rfl
        · rfl
        · exact absurd hm (by decide)
      rw [ex, Nat.xor_div_two, ← e1, hxm]
      omega

theorem testBit_sub_and (m K i : ℕ) : (m - (m &&& K)).testBit i = (m.testBit i && !K.testBit i) := by
  have hd : (m ^^^ (m &&& K)) &&& (m &&& K) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases m.testBit j <;> cases K.testBit j <;> rfl
  have hs := add_eq_xor_of_and _ _ hd
  have hx : (m ^^^ (m &&& K)) ^^^ (m &&& K) = m := by
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hx] at hs
  have e : m - (m &&& K) = m ^^^ (m &&& K) := by omega
  rw [e, Nat.testBit_xor, Nat.testBit_and]
  cases m.testBit i <;> cases K.testBit i <;> rfl

theorem stepOK_inv {MB : List (List ℕ)} {u : ℕ → ZMod 2}
    (hmask : ∀ i r, r < 12 → formVal u (maskAt MB i) r = 0) {K piv : ℕ} {refs : List ℕ}
    (h : stepOK MB oN K piv refs = true) (hK : ∀ β < 4608, K.testBit (12 * β) = true → u β = 0) :
    piv < 4608 ∧ u piv = 0 := by
  change bAnd(Nat.blt piv 4608, Nat.beq (Nat.sub (sumRefs MB oN refs)
    (Nat.land (sumRefs MB oN refs) K)) (Nat.shiftLeft 1 (Nat.mul 12 piv))) = true at h
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hp, e⟩ := h
  have e' := beq_true e
  set m := sumRefs MB oN refs with hm
  have hbit : ∀ β, (m.testBit (12 * β) && !K.testBit (12 * β)) = decide (β = piv) := by
    intro β
    have := congrArg (fun z => Nat.testBit z (12 * β)) e'
    change (m - (m &&& K)).testBit (12 * β) = (1 <<< (12 * piv)).testBit (12 * β) at this
    rw [testBit_sub_and, Nat.one_shiftLeft, Nat.testBit_two_pow] at this
    rw [this, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    omega
  refine ⟨hp, ?_⟩
  have h0 : formVal u m 0 = 0 := formVal_sumRefs hmask refs
  have hs : formVal u m 0 = u piv := by
    unfold formVal
    rw [← Finset.sum_erase_add _ _ (Finset.mem_range.2 hp)]
    have hpb : m.testBit (12 * piv + 0) = true := by
      have := hbit piv
      rw [decide_eq_true rfl, Bool.and_eq_true] at this
      exact this.1
    rw [if_pos hpb, Finset.sum_eq_zero, zero_add]
    intro β hβ
    obtain ⟨hne, hβ'⟩ := Finset.mem_erase.1 hβ
    by_cases hmb : m.testBit (12 * β + 0) = true
    · rw [if_pos hmb]
      have := hbit β
      rw [decide_eq_false hne, Nat.add_zero] at *
      rw [hmb, Bool.true_and, Bool.not_eq_false'] at this
      exact hK β (Finset.mem_range.1 hβ') this
    · rw [if_neg hmb]
  rw [← hs, h0]

theorem echL_inv {MB : List (List ℕ)} {u : ℕ → ZMod 2}
    (hmask : ∀ i r, r < 12 → formVal u (maskAt MB i) r = 0) :
    ∀ (st : List (List ℕ)) (K Kend : ℕ), echL MB oN st K Kend = true →
      (∀ β < 4608, K.testBit (12 * β) = true → u β = 0) →
      ∀ β < 4608, Kend.testBit (12 * β) = true → u β = 0
  | [], K, Kend, h, hK => by
    have e : K = Kend := beq_true h
    rw [← e]
    exact hK
  | [] :: _, _, _, h, _ => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | (piv :: refs) :: st, K, Kend, h, hK => by
    change bAnd(stepOK MB oN K piv refs,
      strictB (Nat.lor K (Nat.shiftLeft 1 (Nat.mul 12 piv))) (fun K' => echL MB oN st K' Kend)) = true
      at h
    rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.strictB_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hp, hu⟩ := stepOK_inv hmask h1 hK
    refine echL_inv hmask st _ Kend h2 fun β hβ hb => ?_
    change (K ||| 1 <<< (12 * piv)).testBit (12 * β) = true at hb
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact hK β hβ hb
    · have : β = piv := by
        have := of_decide_eq_true hb
        omega
      rw [this]
      exact hu

theorem ech_num {YC CKB MB : List (List ℕ)} {ST : List (List (List ℕ))} {KS : List ℕ}
    {MTP LMP GP PP : ℕ}
    (hm : ∀ j < 16, maskBlk YC MTP LMP GP PP CKB MB j = true)
    (he : ∀ i < 6, echChunk MB ST KS i = true)
    (hks : ksK GP PP h2Free KS ST YC aCols bCols yWords = true) (u : ℕ → ZMod 2)
    (hc : ∀ c < 49152, ∀ r < 12, formVal u (cellK YC MTP LMP GP PP oN c) r = 0)
    (hi : ∀ β < 4608, (initK GP PP h2Free).testBit (12 * β) = true → u β = 0)
    (hMB : MB.length = 16) :
    ∀ β < 4608, u β = 0 := by
  obtain ⟨hk0, hk6, -, -⟩ := ksK_parts hks
  have hmask := formVal_maskAt hm hc hMB
  have key : ∀ i ≤ 6, ∀ β < 4608, (getL 0 KS i).testBit (12 * β) = true → u β = 0 := by
    intro i hi6
    induction i with
    | zero => rw [hk0]; exact hi
    | succ i ih =>
      have h := he i (by omega)
      change strictB oN (fun O => echL MB O (getL [] ST i) (getL 0 KS i) (getL 0 KS (Nat.succ i)))
        = true at h
      rw [CFSG.KS.PK.strictB_eq] at h
      exact echL_inv hmask _ _ _ h (ih (by omega))
  intro β hβ
  exact key 6 le_rfl β hβ (by rw [hk6]; exact testBit_oN hβ)

@[expose] noncomputable def valG (g : ↥S → ↥S → V12) (β : ℕ) : ZMod 2 :=
  g (yS (β / 1536)) (elt (β / 12 % 128)) ⟨β % 12, Nat.mod_lt _ (by norm_num)⟩

theorem valG_bitIdx (g : ↥S → ↥S → V12) {k u r : ℕ} (hk : k < 3) (hu : u < 128) (hr : r < 12) :
    valG g (12 * (128 * k + u) + r) = g (yS k) (elt u) ⟨r, hr⟩ := by
  have h1 : (12 * (128 * k + u) + r) / 1536 = k := by omega
  have h2 : (12 * (128 * k + u) + r) / 12 % 128 = u := by omega
  have h3 : (12 * (128 * k + u) + r) % 12 = r := by omega
  simp only [valG, h1, h2, h3]

theorem evalV_unitF_valG (g : ↥S → ↥S → V12) {k x : ℕ} (hk : k < 3) (hx : x < 128) :
    evalV (valG g) (unitF k x) = g (yS k) (elt x) := by
  rw [evalV_unitF _ hk hx]
  funext r
  exact valG_bitIdx g hk hx r.isLt

theorem iter_rec (F : ℕ → ℕ) (x : ℕ) :
    ∀ n, (Nat.rec (motive := fun _ => Nat) x (fun _ ih => F ih) n : ℕ) = F^[n] x
  | 0 => rfl
  | n + 1 => by
    change F (Nat.rec (motive := fun _ => Nat) x (fun _ ih => F ih) n) = _
    rw [iter_rec F x n, Function.iterate_succ_apply']

theorem wF_eval {YC : List (List ℕ)} {KS : List ℕ} {ST : List (List (List ℕ))} {MTP LMP GP PP : ℕ}
    (hks : ksK GP PP h2Free KS ST YC aCols bCols yWords = true) (hdp : depthK PP = true)
    (hd : dataK GP PP LMP genT parT lT = true) (hmt : mtK MTP LMP GP PP = true)
    {ρ : ↥P →* Module.End (ZMod 2) V12} (hρ : IsMRep ρ) {g : ↥S → ↥S → V12}
    (hg : IsNormCoc (rhoS ρ) g) {h : ℕ} (hh : h < 128) :
    ∀ x < 128, evalV (valG g) (wF YC MTP GP PP oN h 8 x) = g (elt x) (elt h) := by
  obtain ⟨hgd, hpd, -⟩ := data_spec hd
  have key : ∀ f x, x < 128 → (fun y => pg 7 127 PP y)^[f] x = 0 →
      evalV (valG g) (wF YC MTP GP PP oN h f x) = g (elt x) (elt h) := by
    intro f
    induction f with
    | zero =>
      intro x _ hx0
      change x = 0 at hx0
      subst hx0
      rw [elt_zero, hg.1]
      exact evalV_zero _
    | succ f ih =>
      intro x hx hit
      by_cases hx0 : x = 0
      · subst hx0
        rw [elt_zero, hg.1]
        exact evalV_zero _
      · have hb : Nat.beq x 0 = false := by
          cases hb : Nat.beq x 0
          · rfl
          · exact absurd (beq_true hb) hx0
        have hpx := par_lt hx0
        have hp : par x < 128 := hpx.trans hx
        change evalV (valG g) (Bool.rec (motive := fun _ => Nat) _ 0 (Nat.beq x 0)) = _
        rw [hb]
        change evalV (valG g) (Nat.xor (Nat.xor (mvI (getL [] YC (pg 2 3 GP x))
          (wF YC MTP GP PP oN h f (pg 7 127 PP x)) oN)
          (unitF (pg 2 3 GP x) (pg 7 127 MTP (Nat.add (Nat.mul 128 (pg 7 127 PP x)) h))))
          (unitF (pg 2 3 GP x) (pg 7 127 PP x))) = _
        have hit' : (fun y => pg 7 127 PP y)^[f] (par x) = 0 := by
          rw [← hpd x hx, ← Function.iterate_succ_apply]
          exact hit
        have hm : pg 7 127 MTP (Nat.add (Nat.mul 128 (par x)) h) = mulIdx (par x) h :=
          mt_spec hmt hd _ hp h hh
        rw [hgd x hx, hpd x hx, hm, evalV_xor, evalV_xor, evalV_mvI hks _ (gen_lt x),
          ih _ hp hit', evalV_unitF_valG g (gen_lt x) (mulIdx_spec hh).1,
          evalV_unitF_valG g (gen_lt x) hp, ← rhoS_yS hρ (gen_lt x), (mulIdx_spec hh).2,
          elt_cons hx0 hx]
        have e := hg.2.2 (yS (gen x)) (elt (par x)) (elt h)
        rw [sub_add_eq_add_sub, sub_eq_zero, sub_eq_iff_eq_add] at e
        rw [e, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  intro x hx
  refine key 8 x hx ?_
  have e := beq_true (CFSG.KS.PK.allN_iff.1 hdp x hx)
  rw [iter_rec] at e
  rw [Function.iterate_succ_apply', e]
  exact (hpd 0 (by norm_num)).trans (by decide)

theorem cellF_eval {YC : List (List ℕ)} {KS : List ℕ} {ST : List (List (List ℕ))} {MTP LMP GP PP : ℕ}
    (hks : ksK GP PP h2Free KS ST YC aCols bCols yWords = true) (hdp : depthK PP = true)
    (hd : dataK GP PP LMP genT parT lT = true) (hmt : mtK MTP LMP GP PP = true)
    {ρ : ↥P →* Module.End (ZMod 2) V12} (hρ : IsMRep ρ) {g : ↥S → ↥S → V12}
    (hg : IsNormCoc (rhoS ρ) g) {k b h : ℕ} (hk : k < 3) (hb : b < 128) (hh : h < 128) :
    evalV (valG g) (cellF YC MTP LMP GP PP oN k b h) = 0 := by
  obtain ⟨-, -, hl⟩ := data_spec hd
  obtain ⟨hlb, hle⟩ := lmul_spec hk hb
  have hm : pg 7 127 MTP (Nat.add (Nat.mul 128 b) h) = mulIdx b h := mt_spec hmt hd b hb h hh
  have hl' : pg 7 127 LMP (Nat.add (Nat.mul 128 k) b) = lmul k b := hl k hk b hb
  change evalV (valG g) (Nat.xor (Nat.xor (mvI (getL [] YC k) (wF YC MTP GP PP oN h 8 b) oN)
      (wF YC MTP GP PP oN h 8 (pg 7 127 LMP (Nat.add (Nat.mul 128 k) b))))
    (Nat.xor (unitF k (pg 7 127 MTP (Nat.add (Nat.mul 128 b) h))) (unitF k b))) = 0
  rw [hl', hm, evalV_xor, evalV_xor, evalV_xor, evalV_mvI hks _ hk,
    wF_eval hks hdp hd hmt hρ hg hh b hb, wF_eval hks hdp hd hmt hρ hg hh _ hlb,
    evalV_unitF_valG g hk (mulIdx_spec hh).1, evalV_unitF_valG g hk hb, ← rhoS_yS hρ hk, hle,
    (mulIdx_spec hh).2]
  have e := hg.2.2 (yS k) (elt b) (elt h)
  simp only [sub_eq_add_neg, neg_eq_self_zmod2] at e
  rw [← e]
  abel

theorem ech_sound {YC CKB MB : List (List ℕ)} {ST : List (List (List ℕ))} {KS : List ℕ}
    {MTP LMP GP PP : ℕ}
    (hm : ∀ j < 16, maskBlk YC MTP LMP GP PP CKB MB j = true)
    (he : ∀ i < 6, echChunk MB ST KS i = true)
    (hks : ksK GP PP h2Free KS ST YC aCols bCols yWords = true) (hdp : depthK PP = true)
    (hd : dataK GP PP LMP genT parT lT = true) (hmt : mtK MTP LMP GP PP = true)
    (hMB : MB.length = 16) {ρ : ↥P →* Module.End (ZMod 2) V12} (hρ : IsMRep ρ) :
    ∀ g : ↥S → ↥S → V12, IsNormCoc (rhoS ρ) g → TreeZero g →
      (∀ i < 30, coordF g (h2Free.getD i 0) = 0) → g = 0 := by
  intro g hg hT hF
  have hu := ech_num hm he hks (valG g) (fun c hc r hr => by
      have hk : c % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hb : c / 3 % 128 < 128 := Nat.mod_lt _ (by norm_num)
      have hh : c / 384 < 128 := by omega
      have e := congrFun (cellF_eval hks hdp hd hmt hρ hg hk hb hh) ⟨r, hr⟩
      exact e)
    (fun β hβ hi => by
      rcases initK_spec hd β hβ hi with ⟨x, hx0, hx, r, hr, rfl⟩ | ⟨i, hi30, rfl⟩
      · rw [valG_bitIdx g (gen_lt x) ((par_lt hx0).trans hx) hr, hT x hx0 hx]
        rfl
      · exact hF i hi30) hMB
  funext s t
  refine eq_zero_of_gen (rhoS ρ) hg (fun k hk t => ?_) s t
  obtain ⟨x, hx, rfl⟩ := elt_surjective t
  funext r
  rw [← valG_bitIdx g hk hx r.isLt]
  exact hu _ (by have := r.isLt; omega)

theorem relation_Hc {HP LMP MTP GP PP BR : ℕ} {SP : List (List ℕ)} {IND DEPA : List ℕ}
    (hrow : ∀ i < 384, rowOKf HP repN LMP MTP SP i = true) (hn : normK HP = true)
    (hrel : ∀ k < 3, relK HP repN LMP BR SP DEPA k = true) (hcov : covK IND DEPA BR = true)
    (hd : dataK GP PP LMP genT parT lT = true) (hmt : mtK MTP LMP GP PP = true)
    (hsp : spyK SP aCols bCols yWords = true) (hSP : ∀ k < 3, (getL [] SP k).length = 12)
    {ρ : ↥P →* Module.End (ZMod 2) V12} (hρ : IsMRep ρ) :
    ∀ j < 30, j ∉ IND.toFinset → ∃ A ⊆ IND.toFinset, ∃ b : ↥S → V12,
      Hc HP j = ∑ i ∈ A, Hc HP i + cob (rhoS ρ) b := by
  intro j hj hjI
  obtain ⟨hI, hb0, hR⟩ := rel_num hrel hcov hd hsp hSP
  obtain ⟨A, hA, hAeq⟩ := hR j hj (fun h => hjI (List.mem_toFinset.2 h))
  refine ⟨A, hA, fun s => bv (hvR BR j (idx s)), ?_⟩
  have hAi : ∀ i ∈ A, i < 30 := fun i hi => hI i (List.mem_toFinset.1 (hA hi))
  refine eq_of_gen (rhoS ρ) (isNormCoc_Hc hrow hn hd hmt hsp hSP hρ hj)
    ((IsNormCoc.sum A fun i hi => isNormCoc_Hc hrow hn hd hmt hsp hSP hρ (hAi i hi)).add
      (isNormCoc_cob _ (by rw [idx_one']; exact hb0 j hj))) fun k hk t => ?_
  obtain ⟨u, hu, rfl⟩ := elt_surjective t
  obtain ⟨hl, hle⟩ := lmul_spec hk hu
  have hy : yS k = elt (k + 1) := (elt_succ hk).symm
  have e := hAeq k hk u hu
  simp only [Pi.add_apply, Finset.sum_apply, CFSG.RankThree.PartTwo.J2Residue.H2.cob]
  rw [← hle, hy, Hc_elt HP j (by omega) hu, idx_elt hu, idx_elt hl, idx_elt (by omega : k + 1 < 128),
    ← hy, rhoS_yS hρ hk]
  have hs : ∑ c ∈ A, Hc HP c (yS k) (elt u) = ∑ i ∈ A, bv (hv HP i (k + 1) u) :=
    Finset.sum_congr rfl fun i _ => by rw [hy, Hc_elt HP i (by omega) hu]
  rw [hs, e, sub_eq_add_neg, neg_eq_self_zmod2]

end CFSG.KC.J2H2

end
