module

public import CFSG.Certificates.Kernel.Spor.ONVecLib
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PWord

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Native
open CFSG.ONSchreier.Native

@[expose] noncomputable def wOfK (X : Nat) : W := ofV ⟨vP X, vM X⟩

@[expose] noncomputable def tabArr (T : Nat → Nat) (n : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => tab T i.val

@[expose] def encL (l : Int) : Nat :=
  if 0 < l then 2 * (l.toNat - 1) else 2 * ((-l).toNat - 1) + 1

@[expose] def encW : List Int → Nat
  | [] => 0
  | l :: w => encW w + encL l * 16 ^ w.length

private theorem ofFn_p (f : Nat → Nat) : ∀ d k,
    (V.ofFn d f).p.testBit k = (decide (k < d) && decide (f k % 3 = 1)) ∧
      (V.ofFn d f).m.testBit k = (decide (k < d) && decide (f k % 3 = 2))
  | 0, k => by simp [V.ofFn, V.zero]
  | d + 1, k => by
    have ih := ofFn_p f d k
    unfold V.ofFn at ih ⊢
    rw [Nat.fold_succ]
    by_cases h1 : f d % 3 = 1
    · simp only [h1, ↓reduceIte]
      rw [Nat.testBit_or, ih.1, Nat.one_shiftLeft, Nat.testBit_two_pow]
      refine ⟨?_, ?_⟩
      · by_cases e : k = d
        · subst e
          simp [h1]
        · have e' : ¬ d = k := fun h => e h.symm
          have h2 : (k < d + 1) ↔ k < d := by omega
          simp [e', h2]
      · rw [ih.2]
        by_cases e : k = d
        · subst e
          simp [h1]
        · have h2 : (k < d + 1) ↔ k < d := by omega
          simp [h2]
    · by_cases h2 : f d % 3 = 2
      · simp only [h2, ↓reduceIte, Nat.reduceEqDiff]
        rw [Nat.testBit_or, ih.2, Nat.one_shiftLeft, Nat.testBit_two_pow]
        refine ⟨?_, ?_⟩
        · rw [ih.1]
          by_cases e : k = d
          · subst e
            simp [h2]
          · have h3 : (k < d + 1) ↔ k < d := by omega
            simp [h3]
        · by_cases e : k = d
          · subst e
            simp [h2]
          · have e' : ¬ d = k := fun h => e h.symm
            have h3 : (k < d + 1) ↔ k < d := by omega
            simp [e', h3]
      · simp only [h1, h2, ↓reduceIte]
        rw [ih.1, ih.2]
        by_cases e : k = d
        · subst e
          simp [h1, h2]
        · have h3 : (k < d + 1) ↔ k < d := by omega
          simp [h3]

private theorem getD_ge {L : List Char} {k : Nat} (h : L.length ≤ k) : L.getD k '0' = '0' := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private noncomputable def digR (R : Nat) (cs : List Char) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ p m => Nat.beq (vmk p m) R)
    (fun ch _ ih j p m => strictB (trit (Char.toNat ch)) fun t =>
      bIf(Nat.blt j (nat_lit 154),
        bIf(Nat.beq t (nat_lit 1), strictB (Nat.lor p (Nat.shiftLeft (nat_lit 1) j)) fun p' =>
            ih (Nat.succ j) p' m,
          bIf(Nat.beq t (nat_lit 2), strictB (Nat.lor m (Nat.shiftLeft (nat_lit 1) j)) fun m' =>
              ih (Nat.succ j) p m',
            ih (Nat.succ j) p m)),
        ih (Nat.succ j) p m))
    cs

private theorem digR_cons (R : Nat) (c : Char) (cs : List Char) (j p m : Nat) :
    digR R (c :: cs) j p m = strictB (trit (Char.toNat c)) fun t =>
      bIf(Nat.blt j (nat_lit 154),
        bIf(Nat.beq t (nat_lit 1), strictB (Nat.lor p (Nat.shiftLeft (nat_lit 1) j)) fun p' =>
            digR R cs (Nat.succ j) p' m,
          bIf(Nat.beq t (nat_lit 2), strictB (Nat.lor m (Nat.shiftLeft (nat_lit 1) j)) fun m' =>
              digR R cs (Nat.succ j) p m',
            digR R cs (Nat.succ j) p m)),
        digR R cs (Nat.succ j) p m) := rfl

private theorem digits_run (L : List Char) (R : Nat) : ∀ r j p m, L.length = j + r →
    (∀ k, p.testBit k = (decide (k < j) && decide (k < 154) &&
      decide (((L.getD k '0').toNat - '0'.toNat) % 3 = 1))) →
    (∀ k, m.testBit k = (decide (k < j) && decide (k < 154) &&
      decide (((L.getD k '0').toNat - '0'.toNat) % 3 = 2))) →
    digR R (L.drop j) j p m = true →
    R = vmk (V.ofFn 154 fun j => (L.getD j '0').toNat - '0'.toNat).p
      (V.ofFn 154 fun j => (L.getD j '0').toNat - '0'.toNat).m
  | 0, j, p, m, hl, hp, hm, h => by
    rw [List.drop_eq_nil_of_le (by omega)] at h
    have hpe : p = (V.ofFn 154 fun j => (L.getD j '0').toNat - '0'.toNat).p :=
      Nat.eq_of_testBit_eq fun k => by
        rw [hp, (ofFn_p _ 154 k).1]
        by_cases hk : k < j
        · simp [hk]
        · have e : L.getD k '0' = '0' := getD_ge (by omega)
          rw [e]
          simp [hk]
    have hme : m = (V.ofFn 154 fun j => (L.getD j '0').toNat - '0'.toNat).m :=
      Nat.eq_of_testBit_eq fun k => by
        rw [hm, (ofFn_p _ 154 k).2]
        by_cases hk : k < j
        · simp [hk]
        · have e : L.getD k '0' = '0' := getD_ge (by omega)
          rw [e]
          simp [hk]
    rw [← hpe, ← hme]
    exact (Nat.eq_of_beq_eq_true h).symm
  | r + 1, j, p, m, hl, hp, hm, h => by
    have hj : j < L.length := by omega
    rw [List.drop_eq_getElem_cons hj] at h
    have hf : ∀ k, k = j → ((L.getD k '0').toNat - '0'.toNat) % 3 = trit (Char.toNat L[j]) := by
      intro k hk
      subst hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    rw [digR_cons, PackFld.strictB_eqP] at h
    have step : ∀ (P M : Nat), (∀ k, P.testBit k = (decide (k < j + 1) && decide (k < 154) &&
          decide (((L.getD k '0').toNat - '0'.toNat) % 3 = 1))) →
        (∀ k, M.testBit k = (decide (k < j + 1) && decide (k < 154) &&
          decide (((L.getD k '0').toNat - '0'.toNat) % 3 = 2))) →
        digR R (L.drop (j + 1)) (j + 1) P M = true → _ :=
      fun P M hP hM hr => digits_run L R r (j + 1) P M (by omega) hP hM hr
    have hsame : ∀ (Q : Nat) (c : Nat), (∀ k, Q.testBit k = (decide (k < j) && decide (k < 154) &&
          decide (((L.getD k '0').toNat - '0'.toNat) % 3 = c))) →
        ¬ (j < 154 ∧ trit (Char.toNat L[j]) = c) →
        ∀ k, Q.testBit k = (decide (k < j + 1) && decide (k < 154) &&
          decide (((L.getD k '0').toNat - '0'.toNat) % 3 = c)) := by
      intro Q c hQ hn k
      rw [hQ]
      by_cases e : k = j
      · subst e
        rw [hf k rfl]
        by_cases h1 : k < 154
        · have : ¬ trit (Char.toNat L[k]) = c := fun h => hn ⟨h1, h⟩
          simp [this]
        · simp [h1]
      · have h3 : (k < j + 1) ↔ k < j := by omega
        simp [h3]
    have hadd : ∀ (Q : Nat) (c : Nat), (∀ k, Q.testBit k = (decide (k < j) && decide (k < 154) &&
          decide (((L.getD k '0').toNat - '0'.toNat) % 3 = c))) →
        j < 154 → trit (Char.toNat L[j]) = c →
        ∀ k, (Nat.lor Q (Nat.shiftLeft 1 j)).testBit k = (decide (k < j + 1) && decide (k < 154) &&
          decide (((L.getD k '0').toNat - '0'.toNat) % 3 = c)) := by
      intro Q c hQ hj1 htc k
      change (Q ||| 1 <<< j).testBit k = _
      rw [Nat.testBit_or, hQ, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases e : k = j
      · subst e
        rw [hf k rfl, htc]
        simp [hj1]
      · have e' : ¬ j = k := fun h => e h.symm
        have h3 : (k < j + 1) ↔ k < j := by omega
        simp [e', h3]
    have hpos : (1 : Nat) ≠ 2 := by decide
    cases hb : Nat.blt j 154 <;> rw [hb] at h
    · have hj1 : ¬ j < 154 := fun x => by rw [Nat.blt_eq.mpr x] at hb; exact Bool.noConfusion hb
      exact step p m (hsame p 1 hp (fun x => hj1 x.1)) (hsame m 2 hm (fun x => hj1 x.1)) h
    · have hj1 : j < 154 := Nat.blt_eq.mp hb
      dsimp only at h
      cases h1 : Nat.beq (trit (Char.toNat L[j])) 1 <;> rw [h1] at h
      · have h1' : trit (Char.toNat L[j]) ≠ 1 := PackFld.false_of_beq h1
        dsimp only at h
        cases h2 : Nat.beq (trit (Char.toNat L[j])) 2 <;> rw [h2] at h
        · have h2' : trit (Char.toNat L[j]) ≠ 2 := PackFld.false_of_beq h2
          exact step p m (hsame p 1 hp (fun x => h1' x.2)) (hsame m 2 hm (fun x => h2' x.2)) h
        · have h2' : trit (Char.toNat L[j]) = 2 := Nat.eq_of_beq_eq_true h2
          dsimp only at h
          rw [PackFld.strictB_eqP] at h
          exact step p _ (hsame p 1 hp (fun x => h1' x.2)) (hadd m 2 hm hj1 h2') h
      · have h1' : trit (Char.toNat L[j]) = 1 := Nat.eq_of_beq_eq_true h1
        dsimp only at h
        rw [PackFld.strictB_eqP] at h
        exact step _ m (hadd p 1 hp hj1 h1') (hsame m 2 hm (fun x => by omega)) h

theorem digitsK_sound {cs : List Char} {R : Nat} (h : digitsK cs R = true) :
    digitsW (String.ofList cs) = wOfK R := by
  have hR := digits_run cs R cs.length 0 0 0 (by omega) (fun k => by simp) (fun k => by simp)
    (by rw [List.drop_zero]; exact h)
  unfold digitsW wOfK
  rw [String.toList_ofList]
  congr 1
  have hp : (V.ofFn 154 fun j => (cs.getD j '0').toNat - '0'.toNat).p < 2 ^ 154 :=
    Nat.lt_pow_two_of_testBit _ fun k hk => by
      rw [(ofFn_p _ 154 k).1]
      simp [show ¬ k < 154 by omega]
  have hm : (V.ofFn 154 fun j => (cs.getD j '0').toNat - '0'.toNat).m < 2 ^ 154 :=
    Nat.lt_pow_two_of_testBit _ fun k hk => by
      rw [(ofFn_p _ 154 k).2]
      simp [show ¬ k < 154 by omega]
  generalize V.ofFn 154 (fun j => (cs.getD j '0').toNat - '0'.toNat) = v at hR hp hm ⊢
  have e1 : vP R = v.p := by
    rw [hR]
    change (v.p ||| v.m <<< 256) &&& mask 256 = v.p
    rw [PackFld.mask_eq]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases hk : k < 256
    · simp [hk, show ¬ k ≥ 256 by omega]
    · have : v.p.testBit k = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hk, this]
  have e2 : vM R = v.m := by
    rw [hR]
    change (v.p ||| v.m <<< 256) >>> 256 = v.m
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
    have : v.p.testBit (256 + k) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this]
  rw [e1, e2]

private noncomputable def dg (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

private noncomputable def entsOf (cs : List Char) : List Nat :=
  (cs.filter fun c => !CFSG.F3.Native.wsChar c).map dg

private theorem beq_char (c d : Char) : (c == d) = (c.toNat == d.toNat) :=
  Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, beq_iff_eq]; exact Char.toNat_inj.symm)

private theorem nbeq (a b : Nat) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b
  · exact (Bool.eq_false_iff.mpr fun e => by rw [beq_iff_eq] at e; subst e; simp at h).symm
  · rw [Nat.eq_of_beq_eq_true h]
    simp

private theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = (c && t || !c && e) := by
  cases c <;> cases t <;> cases e <;> rfl

private theorem wsK_eq (c : Char) : wsK c.toNat = CFSG.F3.Native.wsChar c := by
  unfold wsK CFSG.F3.Native.wsChar
  simp only [bIf_eq, nbeq, beq_char]
  have e1 : (' ' : Char).toNat = 32 := rfl
  have e2 : ('\t' : Char).toNat = 9 := rfl
  have e3 : ('\n' : Char).toNat = 10 := rfl
  have e4 : ('\r' : Char).toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  cases (c.toNat == 32) <;> cases (c.toNat == 9) <;> cases (c.toNat == 10) <;>
    cases (c.toNat == 13) <;> cases (c.toNat == 11) <;> cases (c.toNat == 12) <;> rfl

private theorem entK_eq (c : Char) : entK c.toNat = dg c := by
  unfold entK dg
  have h1 : ('0' ≤ c) ↔ 48 ≤ c.toNat := by
    change ('0' : Char).val ≤ c.val ↔ _
    rw [UInt32.le_iff_toNat_le]
    rfl
  have h2 : (c ≤ '9') ↔ c.toNat ≤ 57 := by
    change c.val ≤ ('9' : Char).val ↔ _
    rw [UInt32.le_iff_toNat_le]
    rfl
  have e0 : ('0' : Char).toNat = 48 := rfl
  by_cases a : c.toNat < 48
  · have : Nat.blt c.toNat 48 = true := Nat.blt_eq.mpr a
    rw [this]
    have : ¬ ('0' ≤ c) := fun x => by rw [h1] at x; omega
    simp [this]
  · have : Nat.blt c.toNat 48 = false := by
      cases e : Nat.blt c.toNat 48
      · rfl
      · exact absurd (Nat.blt_eq.mp e) a
    rw [this]
    by_cases b : c.toNat < 58
    · have : Nat.blt c.toNat 58 = true := Nat.blt_eq.mpr b
      rw [this]
      have x1 : '0' ≤ c := by rw [h1]; omega
      have x2 : c ≤ '9' := by rw [h2]; omega
      simp [x1, x2, e0]
    · have : Nat.blt c.toNat 58 = false := by
        cases e : Nat.blt c.toNat 58
        · rfl
        · exact absurd (Nat.blt_eq.mp e) b
      rw [this]
      have x2 : ¬ c ≤ '9' := fun x => by rw [h2] at x; omega
      simp [x2]

private theorem colsBody_spec {C : Nat → Nat} : ∀ (cs : List Char) (k : Nat),
    colsBody C cs k = true → 23716 ≤ k + (entsOf cs).length ∧
      ∀ idx (hi : idx < (entsOf cs).length), k + idx < 23716 →
        colEnt C (k + idx) (entsOf cs)[idx] = true
  | [], k, h => by
    have : 23716 ≤ k := Nat.le_of_ble_eq_true h
    exact ⟨by simpa [entsOf] using this, fun idx hi => absurd hi (by simp [entsOf])⟩
  | ch :: cs, k, h => by
    change strictB (Char.toNat ch) (fun c =>
      bIf(wsK c, colsBody C cs k,
        bIf(Nat.blt k (nat_lit 23716), bAnd(colEnt C k (entK c), colsBody C cs (Nat.succ k)),
          colsBody C cs (Nat.succ k)))) = true at h
    rw [PackFld.strictB_eqP, wsK_eq] at h
    cases hw : CFSG.F3.Native.wsChar ch <;> rw [hw] at h
    · have e : entsOf (ch :: cs) = dg ch :: entsOf cs := by
        simp [entsOf, hw]
      rw [e]
      cases hb : Nat.blt k 23716 <;> rw [hb] at h
      · have hk : 23716 ≤ k := by
          cases e2 : decide (k < 23716)
          · simpa using e2
          · rw [Nat.blt_eq.mpr (by simpa using e2)] at hb
            exact Bool.noConfusion hb
        obtain ⟨a, -⟩ := colsBody_spec cs (k + 1) h
        refine ⟨by simp; omega, fun idx hi hk' => absurd hk' (by omega)⟩
      · rw [bAnd_iff] at h
        obtain ⟨a, b⟩ := colsBody_spec cs (k + 1) h.2
        refine ⟨by simp; omega, fun idx hi hk' => ?_⟩
        rcases idx with _ | idx
        · rw [← entK_eq]
          exact h.1
        · rw [List.getElem_cons_succ, show k + (idx + 1) = k + 1 + idx by omega]
          exact b idx (by simpa using hi) (by omega)
    · have e : entsOf (ch :: cs) = entsOf cs := by
        simp [entsOf, hw]
      rw [e]
      exact colsBody_spec cs k h

private theorem colsHead_spec {C : Nat → Nat} : ∀ cs : List Char, colsHead C cs = true →
    colsBody C ((cs.dropWhile (· != '\n')).drop 1) 0 = true
  | [], h => absurd h Bool.false_ne_true
  | ch :: cs, h => by
    change Bool.rec (motive := fun _ => Bool) (colsHead C cs) (colsBody C cs 0)
      (Nat.beq (Char.toNat ch) 10) = true at h
    cases hb : Nat.beq (Char.toNat ch) 10 <;> rw [hb] at h
    · have hne : (ch != '\n') = true := by
        rw [bne, beq_char]
        have : ('\n' : Char).toNat = 10 := rfl
        rw [this, ← nbeq, hb]
        rfl
      rw [List.dropWhile_cons_of_pos (p := fun x => x != '\n') hne]
      exact colsHead_spec cs h
    · have hne : (ch != '\n') = false := by
        rw [bne, beq_char]
        have : ('\n' : Char).toNat = 10 := rfl
        rw [this, ← nbeq, hb]
        rfl
      rw [List.dropWhile_cons_of_neg (p := fun x => x != '\n') (by simp [hne])]
      exact h

private theorem bit_eq (x j : Nat) : bit x j = x.testBit j := by
  unfold bit
  have e : Nat.land (Nat.shiftRight x j) 1 = x / 2 ^ j % 2 := by
    change (x >>> j) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq, nbeq]
  cases h : decide (x / 2 ^ j % 2 = 1)
  · simp at h
    simp [h]
  · simp at h
    simp [h]

private theorem colEnt_spec {C : Nat → Nat} {i j e : Nat} (hj : j < 154)
    (h : colEnt C (i * 154 + j) e = true) :
    (vP (C j)).testBit i = decide (e % 3 = 1) ∧ (vM (C j)).testBit i = decide (e % 3 = 2) := by
  have hi : (i * 154 + j) / 154 = i := by omega
  have hm : (i * 154 + j) % 154 = j := by omega
  unfold colEnt at h
  simp only [PackFld.strictB_eqP] at h
  change bAnd(Bool.rec (motive := fun _ => Bool) (Bool.not (Nat.beq (e % 3) 1))
      (Nat.beq (e % 3) 1) (bit (vP (C ((i * 154 + j) % 154))) ((i * 154 + j) / 154)),
    Bool.rec (motive := fun _ => Bool) (Bool.not (Nat.beq (e % 3) 2))
      (Nat.beq (e % 3) 2) (bit (vM (C ((i * 154 + j) % 154))) ((i * 154 + j) / 154))) = true at h
  rw [hi, hm, bAnd_iff, bit_eq, bit_eq] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · cases hb : (vP (C j)).testBit i <;> rw [hb] at h1
    · have : Nat.beq (e % 3) 1 = false := by simpa using h1
      have := PackFld.false_of_beq this
      simp [this]
    · simp [Nat.eq_of_beq_eq_true h1]
  · cases hb : (vM (C j)).testBit i <;> rw [hb] at h2
    · have : Nat.beq (e % 3) 2 = false := by simpa using h2
      have := PackFld.false_of_beq this
      simp [this]
    · simp [Nat.eq_of_beq_eq_true h2]

theorem colsK_sound {C : Nat → Nat} {cs : List Char} (h : colsK C cs = true) :
    ∀ j < 154, ((transpose 154 (rowsOf 154 (String.ofList cs))).map ofV)[j]! = wOfK (C j) := by
  intro j hj
  unfold colsK at h
  rw [bAnd_iff] at h
  obtain ⟨hcan, hh⟩ := h
  obtain ⟨hlen, hent⟩ := colsBody_spec _ 0 (colsHead_spec cs hh)
  have hdec : CFSG.F3.Native.decodeEntries (String.ofList cs) =
      entsOf ((cs.dropWhile (· != '\n')).drop 1) := by
    unfold CFSG.F3.Native.decodeEntries entsOf dg
    rw [String.toList_ofList]
  generalize entsOf ((cs.dropWhile (· != '\n')).drop 1) = E at hdec hlen hent
  have hc := allN_spec hcan j hj
  unfold canon at hc
  simp only [PackFld.strictB_eqP, bAnd_iff] at hc
  obtain ⟨-, hp, hm⟩ := hc
  have hp' : vP (C j) < 2 ^ 154 := by
    have := Nat.blt_eq.mp hp
    rwa [PackFld.shl_eq, Nat.one_mul] at this
  have hm' : vM (C j) < 2 ^ 154 := by
    have := Nat.blt_eq.mp hm
    rwa [PackFld.shl_eq, Nat.one_mul] at this
  rw [getElem!_pos _ j (by simp [transpose, hj]), Array.getElem_map]
  unfold wOfK transpose
  rw [Array.getElem_ofFn]
  congr 1
  have key : ∀ i < 154, ((rowsOf 154 (String.ofList cs))[i]!.get j) % 3 = E[i * 154 + j]! % 3 ∧
      (vP (C j)).testBit i = decide (E[i * 154 + j]! % 3 = 1) ∧
      (vM (C j)).testBit i = decide (E[i * 154 + j]! % 3 = 2) := by
    intro i hi
    have hidx : i * 154 + j < E.length := by omega
    have hce := hent (i * 154 + j) hidx (by omega)
    rw [Nat.zero_add] at hce
    rw [getElem!_pos E _ hidx]
    refine ⟨?_, colEnt_spec hj hce⟩
    unfold rowsOf
    rw [getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]
    unfold V.get
    rw [(ofFn_p _ 154 j).1, (ofFn_p _ 154 j).2, hdec]
    simp only [hj, decide_true, Bool.true_and, List.getElem?_toArray, List.getElem?_eq_getElem hidx,
      Option.getD_some]
    have h3 := Nat.mod_lt E[i * 154 + j] (by decide : 3 > 0)
    by_cases a : E[i * 154 + j] % 3 = 1
    · simp [a]
    · by_cases b : E[i * 154 + j] % 3 = 2
      · simp [b]
      · have : E[i * 154 + j] % 3 = 0 := by omega
        simp [this]
  have e1 : (V.ofFn 154 fun i => (rowsOf 154 (String.ofList cs))[i]!.get j).p = vP (C j) :=
    Nat.eq_of_testBit_eq fun i => by
      rw [(ofFn_p _ 154 i).1]
      by_cases hi : i < 154
      · rw [(key i hi).2.1, (key i hi).1]
        simp [hi]
      · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp' (Nat.pow_le_pow_right (by omega)
          (by omega)))]
        simp [hi]
  have e2 : (V.ofFn 154 fun i => (rowsOf 154 (String.ofList cs))[i]!.get j).m = vM (C j) :=
    Nat.eq_of_testBit_eq fun i => by
      rw [(ofFn_p _ 154 i).2]
      by_cases hi : i < 154
      · rw [(key i hi).2.2, (key i hi).1]
        simp [hi]
      · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by omega)
          (by omega)))]
        simp [hi]
  rw [← e1, ← e2]

theorem bits_sound {Y : Nat} (h : canon Y = true) {t : Nat} (ht : t < 154) :
    (wOfK Y).bitP t = bit (vP Y) t ∧ (wOfK Y).bitM t = bit (vM Y) t := by
  have _ := h
  rw [bit_eq, bit_eq]
  exact bit_ofV (vOf Y) (by omega)

theorem canon_sound {X : Nat} (h : canon X = true) : canon154 (wOfK X) = true := canon154_vOf h

theorem wOfK_inj {X Y : Nat} (hX : canon X = true) (hY : canon Y = true) (h : wOfK X = wOfK Y) :
    X = Y := vOf_inj hX hY h

theorem mv_sound {cA : Array W} {LA : List Nat}
    (hcA : cA.size = 154 ∧ LA.length = 154 ∧ ∀ j < 154, cA[j]! = wOfK (LA.getD j 0))
    (hCA : ∀ j < 154, canon (LA.getD j 0) = true) {X : Nat} (hX : canon X = true) :
    mulVecT cA (wOfK X) = wOfK (mv LA X) := by
  have _ := hX
  exact mulVecT_vOf hcA hCA X

theorem bfsK_sim {cA cB : Array W} {root : W} {n SL NS : Nat}
    {K A B SO SOI NX : Nat → Nat} {LA LB : List Nat}
    (hcA : cA.size = 154 ∧ LA.length = 154 ∧ ∀ j < 154, cA[j]! = wOfK (LA.getD j 0))
    (hcB : cB.size = 154 ∧ LB.length = 154 ∧ ∀ j < 154, cB[j]! = wOfK (LB.getD j 0))
    (hCA : ∀ j < 154, canon (LA.getD j 0) = true) (hCB : ∀ j < 154, canon (LB.getD j 0) = true)
    (hr : root = wOfK (key K 0)) (hn : 0 < n ∧ n < 2 ^ 18)
    (hmv : ∀ h < n, mvAt K LA LB A B n h = true)
    (hNS : NS * SL = n) (hX0 : NX 0 = 1) (hXN : NX NS = n)
    (hord : ∀ s < NS, Nat.beq (ordRun A B (s * SL) SL (NX s)) (NX (s + 1)) = true)
    (hsort : ∀ i < n, sortAt K SO SOI n i = true) :
    (orbitBFS cA cB root n).keys = (Array.ofFn (n := n) fun i => wOfK (key K i.val)) ∧
      natTab (orbitBFS cA cB root n).alpha = tabArr A n ∧
      natTab (orbitBFS cA cB root n).beta = tabArr B n :=
  bfs_sim hcA hcB hCA hCB hr hn hmv hNS hX0 hXN hord hsort

theorem bfsK_sound {cA cB : Array W} {root : W} {n SL NS : Nat}
    {K A B SO SOI NX : Nat → Nat} {LA LB : List Nat}
    (hcA : cA.size = 154 ∧ LA.length = 154 ∧ ∀ j < 154, cA[j]! = wOfK (LA.getD j 0))
    (hcB : cB.size = 154 ∧ LB.length = 154 ∧ ∀ j < 154, cB[j]! = wOfK (LB.getD j 0))
    (hCA : ∀ j < 154, canon (LA.getD j 0) = true) (hCB : ∀ j < 154, canon (LB.getD j 0) = true)
    (hr : root = wOfK (key K 0)) (hn : 0 < n ∧ n < 2 ^ 18)
    (hmv : ∀ h < n, mvAt K LA LB A B n h = true)
    (hNS : NS * SL = n) (hX0 : NX 0 = 1) (hXN : NX NS = n)
    (hord : ∀ s < NS, Nat.beq (ordRun A B (s * SL) SL (NX s)) (NX (s + 1)) = true)
    (hsort : ∀ i < n, sortAt K SO SOI n i = true) :
    natTab (orbitBFS cA cB root n).alpha = tabArr A n ∧
      natTab (orbitBFS cA cB root n).beta = tabArr B n :=
  (bfsK_sim hcA hcB hCA hCB hr hn hmv hNS hX0 hXN hord hsort).2

private theorem letterOfCode_encL {l : Int} (h0 : l ≠ 0) (h8 : l.natAbs ≤ 8) :
    encL l < 16 ∧ CFSG.KS.Words.letterOfCode (encL l) = l := by
  unfold encL CFSG.KS.Words.letterOfCode
  by_cases hp : 0 < l
  · rw [ite_eq_left hp]
    refine ⟨by omega, ?_⟩
    rw [ite_eq_left (by omega)]
    omega
  · rw [ite_eq_right hp]
    refine ⟨by omega, ?_⟩
    rw [ite_eq_right (by omega)]
    omega

private theorem encW_lt : ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 8) →
    encW w < 16 ^ w.length
  | [], _ => by simp [encW]
  | l :: w, h => by
    have ih := encW_lt w fun z hz => h z (List.mem_cons_of_mem l hz)
    have hl := (letterOfCode_encL (h l List.mem_cons_self).1 (h l List.mem_cons_self).2).1
    simp only [encW, List.length_cons, Nat.pow_succ]
    have : encL l * 16 ^ w.length ≤ 15 * 16 ^ w.length := Nat.mul_le_mul_right _ (by omega)
    omega

private theorem shr4 (W k : Nat) : W >>> (4 * k) = W / 16 ^ k := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

private theorem decW_congr {W W' : Nat} : ∀ L, (∀ k < L, (W >>> (4 * k)) % 16 = (W' >>> (4 * k)) % 16) →
    CFSG.KS.Words.decW W L = CFSG.KS.Words.decW W' L
  | 0, _ => rfl
  | L + 1, h => by
    rw [CFSG.KS.Words.decW, CFSG.KS.Words.decW, h L (by omega),
      decW_congr L fun k hk => h k (by omega)]

private theorem decW_encW : ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 8) →
    CFSG.KS.Words.decW (encW w) w.length = w
  | [], _ => rfl
  | l :: w, h => by
    have hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 8 := fun z hz => h z (List.mem_cons_of_mem l hz)
    obtain ⟨hl, hc⟩ := letterOfCode_encL (h l List.mem_cons_self).1 (h l List.mem_cons_self).2
    have hlt := encW_lt w hw
    have hpos : 0 < 16 ^ w.length := Nat.pow_pos (by omega)
    simp only [encW, List.length_cons]
    rw [CFSG.KS.Words.decW]
    congr 1
    · rw [shr4, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add,
        Nat.mod_eq_of_lt hl, hc]
    · rw [decW_congr (W' := encW w) w.length fun k hk => ?_]
      · exact decW_encW w hw
      · rw [shr4, shr4]
        have e : 16 ^ w.length = 16 ^ k * (16 * 16 ^ (w.length - k - 1)) := by
          rw [← Nat.pow_succ', ← Nat.pow_add]
          congr 1
          omega
        have hk' : 0 < 16 ^ k := Nat.pow_pos (by omega)
        have e2 : encL l * 16 ^ w.length = 16 * (encL l * 16 ^ (w.length - k - 1)) * 16 ^ k := by
          rw [e]
          ac_rfl
        rw [e2, Nat.add_mul_div_right _ _ hk', Nat.add_mul_mod_self_left]

theorem strongK_sound {n nT : Nat} {TT UU : Nat → Nat → Nat} {WC WL : Nat → Nat}
    {words : Array (List Int)} (hw : words.size = nT) (h2 : 2 ≤ nT) (h9 : nT ≤ 9)
    (h01 : words[0]! = [] ∧ words[1]! = [])
    (henc : ∀ j < nT, 2 ≤ j → encW words[j]! = WC j ∧ (words[j]!).length = WL j ∧
      plettersOK j words[j]! = true)
    (htr : ∀ x < n, trAt TT UU WC WL n nT 2 x = true) :
    strongArrs n (Array.ofFn (n := n) fun i => TT 0 i.val) (Array.ofFn (n := n) fun i => TT 1 i.val)
      words = Array.ofFn (n := nT) fun j => Array.ofFn (n := n) fun i => TT j.val i.val := by
  have _ := h01
  have hlet : ∀ j < nT, 2 ≤ j → ∀ l ∈ words[j]!, l ≠ 0 ∧ l.natAbs ≤ j := by
    intro j hj h2j l hl
    have := List.all_eq_true.1 (henc j hj h2j).2.2 l hl
    simpa using this
  have hdec : ∀ j < nT, 2 ≤ j → CFSG.KS.Words.decW (WC j) (WL j) = words[j]! := by
    intro j hj h2j
    obtain ⟨e1, e2, -⟩ := henc j hj h2j
    rw [← e1, ← e2]
    exact decW_encW _ fun l hl => ⟨(hlet j hj h2j l hl).1, by have := (hlet j hj h2j l hl).2; omega⟩
  have hpt : ∀ x < n, (∀ h < nT, TT h x < n ∧ UU h x < n ∧ UU h (TT h x) = x) ∧
      ∀ j < nT, 2 ≤ j → TT j x = trace TT UU (WC j) (WL j) x := by
    intro x hx
    have h := htr x hx
    unfold trAt at h
    obtain ⟨hA, hB⟩ := (bAnd_iff _ _).1 h
    refine ⟨fun h' hh => ?_, fun j hj h2j => ?_⟩
    · have h3 := allBlk_spec hA h' hh
      rw [Nat.add_eq, Nat.zero_add, PackFld.strictB_eqP] at h3
      obtain ⟨a1, h4⟩ := (bAnd_iff _ _).1 h3
      obtain ⟨a2, a3⟩ := (bAnd_iff _ _).1 h4
      exact ⟨Nat.blt_eq.mp a1, Nat.blt_eq.mp a2, Nat.eq_of_beq_eq_true a3⟩
    · have h3 := allBlk_spec hB (j - 2) (by change j - 2 < nT - 2; omega)
      rw [Nat.add_eq, show 2 + (j - 2) = j by omega] at h3
      exact Nat.eq_of_beq_eq_true h3
  obtain ⟨hs, hg⟩ := CFSG.KS.PW.extendStrong_get (n := n) (m := 2) (s := nT)
    (orig := #[Array.ofFn (n := n) fun i => TT 0 i.val, Array.ofFn (n := n) fun i => TT 1 i.val])
    (W := words) (F := TT) (FI := UU) rfl hw h2
    (fun j hj => by
      rcases j with _ | _ | j
      · rfl
      · rfl
      · omega)
    (fun j h2j hj => ⟨hlet j hj h2j, fun x hx => by
      rw [(hpt x hx).2 j hj h2j, CFSG.KS.TW.trace_eq, hdec j hj h2j]⟩)
    (fun j hj x hx => (hpt x hx).1 j hj)
  unfold strongArrs
  apply Array.ext
  · rw [hs, Array.size_ofFn]
  · intro i h1 h3
    have hi : i < nT := by simpa using h3
    rw [← getElem!_pos _ i h1, hg i hi, Array.getElem_ofFn]

end CFSG.KS.ON

end
