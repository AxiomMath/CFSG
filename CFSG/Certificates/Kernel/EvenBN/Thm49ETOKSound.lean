module

public import Certificates.Data.Kernel.EvenBN.Thm49ETO
public import CFSG.Certificates.Kernel.EvenBN.Thm49EF6Sound

public section

namespace CFSG.KD.T49

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2

theorem field_disj {w i j k : Nat} (hk : k < w) (hij : j ≠ i) :
    w * j + k < w * i ∨ w * i + w ≤ w * j + k := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · left
    have : w * (j + 1) ≤ w * i := Nat.mul_le_mul_left w h
    rw [Nat.mul_succ] at this
    omega
  · right
    have : w * (i + 1) ≤ w * j := Nat.mul_le_mul_left w h
    rw [Nat.mul_succ] at this
    omega

theorem tg_tsetK {w T i v j : Nat} (hv : v < 2 ^ w) :
    tg w (tsetK w T i v) j = if j = i then v else tg w T j := by
  have key : ∀ k, (tg w (tsetK w T i v) j).testBit k = (decide (k < w) &&
      ((T.testBit (w * j + k) ^^ (T.testBit (w * j + k) &&
        (decide (w * j + k ≥ w * i) && decide (w * j + k - w * i < w)))) ||
        (decide (w * j + k ≥ w * i) && v.testBit (w * j + k - w * i)))) := by
    intro k
    unfold tg
    rw [CFSG.KS.PF.testBit_pgM]
    unfold tsetK
    change (decide (k < w) && ((T ^^^ (T &&& (mask w <<< (w * i)))) ||| (v <<< (w * i))).testBit
      (w * j + k)) = _
    rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft,
      Nat.testBit_shiftLeft, CFSG.KS.PF.mask_eq, Nat.testBit_two_pow_sub_one]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [key]
    by_cases hk : k < w
    · have e : w * j + k - w * j = k := by omega
      simp [hk, e]
    · have hv' : v.testBit k = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hk, hv']
  · rw [if_neg hji]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [key]
    unfold tg
    rw [CFSG.KS.PF.testBit_pgM]
    by_cases hk : k < w
    · rcases field_disj hk hji with h | h
      · have h1 : ¬ (w * j + k ≥ w * i) := by omega
        simp [hk, h1]
      · have h1 : ¬ (w * j + k - w * i < w) := by omega
        have hv' : v.testBit (w * j + k - w * i) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num)
            (by omega)))
        simp [hk, h1, hv']
    · simp [hk]

theorem tg_lt (w T i : Nat) : tg w T i < 2 ^ w := CFSG.KS.PF.pg_lt w T i

theorem lt128_of_lt92 {v : Nat} (h : v < 92) : v < 2 ^ 7 := by
  have : (2 : Nat) ^ 7 = 128 := by norm_num
  omega

@[expose] noncomputable def rowPart (f : Nat → Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun m ih => tsetK 7 ih m (f m)) k

theorem tg_zero (w j : Nat) : tg w 0 j = 0 := by
  unfold tg pg
  simp

theorem tg_recSet {w : Nat} {f : Nat → Nat} :
    ∀ k, (∀ m < k, f m < 2 ^ w) → ∀ j,
      tg w (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun m ih => tsetK w ih m (f m)) k) j =
      if j < k then f j else 0
  | 0, _, j => by
    rw [if_neg (Nat.not_lt_zero j)]
    exact tg_zero w j
  | k + 1, hf, j => by
    change tg w (tsetK w (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun m ih => tsetK w ih m (f m)) k) k (f k)) j = _
    rw [tg_tsetK (hf k (by omega)), tg_recSet k (fun m hm => hf m (by omega)) j]
    by_cases h : j = k
    · subst h
      simp
    · rw [if_neg h]
      by_cases h' : j < k
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg (by omega)]

theorem tg_rowK {f : Nat → Nat} (hf : ∀ m < 92, f m < 2 ^ 7) {m : Nat} (hm : m < 92) :
    tg 7 (rowK f) m = f m := by
  have := tg_recSet 92 hf m
  rw [if_pos hm] at this
  exact this

theorem testBit_tsetK_hi {w T i v b : Nat} (hv : v < 2 ^ w) (hT : T.testBit b = false)
    (hb : w * i + w ≤ b) : (tsetK w T i v).testBit b = false := by
  unfold tsetK
  change ((T ^^^ (T &&& (mask w <<< (w * i)))) ||| (v <<< (w * i))).testBit b = false
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, hT]
  have hv' : v.testBit (b - w * i) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
  simp [hv']

theorem rowPart_testBit {f : Nat → Nat} :
    ∀ k, (∀ m < k, f m < 2 ^ 7) → ∀ b, 7 * k ≤ b → (rowPart f k).testBit b = false
  | 0, _, b, _ => by simp [rowPart]
  | k + 1, hf, b, hb => by
    change (tsetK 7 (rowPart f k) k (f k)).testBit b = false
    exact testBit_tsetK_hi (hf k (by omega))
      (rowPart_testBit k (fun m hm => hf m (by omega)) b (by omega)) (by omega)

theorem rowK_shr {f : Nat → Nat} (hf : ∀ m < 92, f m < 2 ^ 7) : rowK f >>> (92 * 7) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_shiftRight, Nat.zero_testBit]
  exact rowPart_testBit 92 hf _ (by omega)

@[expose] noncomputable def qPart (p K : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x ih => tsetK 7 ih (tg 7 p x) (tg 7 p (tg 7 K x))) k

theorem tg_qPart {p K : Nat} (hinj : ∀ x < 92, ∀ y < 92, tg 7 p x = tg 7 p y → x = y) :
    ∀ k ≤ 92, ∀ x < k, tg 7 (qPart p K k) (tg 7 p x) = tg 7 p (tg 7 K x)
  | 0, _, x, hx => absurd hx (Nat.not_lt_zero x)
  | k + 1, hk, x, hx => by
    change tg 7 (tsetK 7 (qPart p K k) (tg 7 p k) (tg 7 p (tg 7 K k))) (tg 7 p x) = _
    rw [tg_tsetK (tg_lt 7 p _)]
    by_cases h : x = k
    · subst h
      simp
    · rw [if_neg (fun e => h (hinj x (by omega) k (by omega) e))]
      exact tg_qPart hinj k (by omega) x (by omega)

theorem tg_qRowK {p K : Nat} (hinj : ∀ x < 92, ∀ y < 92, tg 7 p x = tg 7 p y → x = y) {x : Nat}
    (hx : x < 92) : tg 7 (qRowK p K) (tg 7 p x) = tg 7 p (tg 7 K x) :=
  tg_qPart hinj 92 le_rfl x hx

theorem qPart_testBit {p K : Nat} (hp : ∀ x < 92, tg 7 p x < 92) :
    ∀ k ≤ 92, ∀ b, 7 * 92 ≤ b → (qPart p K k).testBit b = false
  | 0, _, b, _ => by simp [qPart]
  | k + 1, hk, b, hb => by
    change (tsetK 7 (qPart p K k) (tg 7 p k) (tg 7 p (tg 7 K k))).testBit b = false
    have h1 := hp k (by omega)
    exact testBit_tsetK_hi (tg_lt 7 p _) (qPart_testBit hp k (by omega) b hb) (by omega)

theorem qRowK_shr {p K : Nat} (hp : ∀ x < 92, tg 7 p x < 92) : qRowK p K >>> (92 * 7) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_shiftRight, Nat.zero_testBit]
  exact qPart_testBit hp 92 le_rfl _ (by omega)

theorem eq_of_rows {A B : Nat} (hA : A >>> (92 * 7) = 0) (hB : B >>> (92 * 7) = 0)
    (h : ∀ m < 92, tg 7 A m = tg 7 B m) : A = B :=
  CFSG.KS.PF.eq_of_fields (n := 92) (w := 7) (by norm_num) hA hB h

theorem nthK_eq : ∀ (l : List Nat) (i : Nat), nthK l i = l.getD i 0
  | [], _ => rfl
  | x :: l, 0 => rfl
  | x :: l, i + 1 => by
    change nthK l i = _
    rw [nthK_eq l i]
    rfl

theorem nthW_eq : ∀ (l : List (List Int)) (i : Nat), nthW l i = l.getD i []
  | [], _ => rfl
  | x :: l, 0 => rfl
  | x :: l, i + 1 => by
    change nthW l i = _
    rw [nthW_eq l i]
    rfl

theorem memK_iff (x : Nat) : ∀ l : List Nat, memK x l = true ↔ x ∈ l
  | [] => by simp [memK]
  | y :: l => by
    change Bool.rec (motive := fun _ => Bool) (memK x l) true (Nat.beq x y) = true ↔ _
    rw [CFSG.KS.Raw.Orb.bIf_eq, List.mem_cons]
    by_cases h : x = y
    · subst h
      simp
    · rw [if_neg (by rw [Nat.beq_eq]; exact h), memK_iff x l]
      simp [h]

theorem maskL_iff (y : Nat) : ∀ l : List Nat, bitK (maskL l) y = true ↔ y ∈ l
  | [] => by simp [maskL, bitK_zero]
  | x :: l => by
    change bitK (setK (maskL l) x) y = true ↔ _
    rw [bitK_setK, maskL_iff y l, List.mem_cons]
    tauto

theorem mapFy_eq : ∀ l : List Nat, mapFy l = l.map fy
  | [] => rfl
  | r :: l => by
    change fy r :: mapFy l = _
    rw [mapFy_eq l]
    rfl

theorem getD_eq_idx {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := (List.getElem_eq_getD d).symm

theorem tg_fzIdxAux : ∀ (l : List Nat) (i : Nat), l.Nodup → i + l.length < 2 ^ 7 →
    ∀ j < l.length, tg 7 ((List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
      (fun y _ ih i => tsetK 7 (ih (Nat.succ i)) y (Nat.succ i)) l) i) (l.getD j 0) = i + j + 1
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | y :: l, i, hnd, hb, j, hj => by
    change tg 7 (tsetK 7 ((List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
      (fun y _ ih i => tsetK 7 (ih (Nat.succ i)) y (Nat.succ i)) l) (Nat.succ i)) y (Nat.succ i))
      ((y :: l).getD j 0) = _
    have hlt : Nat.succ i < 2 ^ 7 := by
      simp only [List.length_cons] at hb
      omega
    rw [tg_tsetK hlt]
    rw [List.nodup_cons] at hnd
    rcases j with _ | j
    · simp
    · simp only [List.getD_cons_succ]
      have hj' : j < l.length := by simpa using hj
      have hne : l.getD j 0 ≠ y := by
        intro e
        apply hnd.1
        rw [← e, getD_eq_idx hj']
        exact List.getElem_mem hj'
      rw [if_neg hne, tg_fzIdxAux l (Nat.succ i) hnd.2 (by
        simp only [List.length_cons] at hb
        omega) j hj']
      omega

theorem tg_fzIdx {fz : List Nat} (hnd : fz.Nodup) (hlen : fz.length < 2 ^ 7) {j : Nat}
    (hj : j < fz.length) : tg 7 (fzIdx fz) (fz.getD j 0) = j + 1 := by
  have := tg_fzIdxAux fz 0 hnd (by omega) j hj
  rw [Nat.zero_add] at this
  exact this

theorem lpt_eq (S SI : Nat → Nat) (z : Int) (x : Nat) :
    lpt S SI z x = ap (nIf(Nat.beq (Nat.land (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 0),
      S (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 1)),
      SI (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 1)))) x := by
  unfold lpt
  rw [strictN_eq]

theorem ap_pmul {P Q x : Nat} (hx : x < 1755) : ap (pmul P Q) x = ap P (ap Q x) :=
  CFSG.KS.PF.pg_pcomp (by norm_num) hx

theorem ap_idP {x : Nat} (hx : x < 1755) : ap idP x = x :=
  CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hx

theorem wpt_eq_ap (S SI : Nat → Nat) : ∀ (w : List Int) {x : Nat}, x < 1755 →
    wpt S SI w x = ap (wd S SI w) x
  | [], x, hx => by
    change x = ap idP x
    rw [ap_idP hx]
  | z :: w, x, hx => by
    change lpt S SI z (wpt S SI w x) = ap (wordK 1755 11 (mask 11) idP S SI (z :: w)) x
    rw [wordK_cons, lpt_eq]
    change _ = ap (pmul _ _) x
    rw [ap_pmul hx, wpt_eq_ap S SI w hx]
    rfl

theorem wpt_eq {k : Nat} {S SI : Nat → Nat} {gs : Nat → Equiv.Perm (Fin 1755)}
    (hS : ∀ j < k, PR (S j) (gs j)) (hSI : ∀ j < k, PR (SI j) (gs j)⁻¹) {w : List Int}
    (hl : lettersK k w = true) (x : Fin 1755) :
    wpt S SI w x = (wordIn k gs w x : Nat) := by
  rw [wpt_eq_ap S SI w x.2, ap_eq (prep_wd hS hSI hl) x]

theorem wordIn_single_inv {k : Nat} (gs : Nat → Equiv.Perm (Fin 1755)) (z : Int) :
    wordIn k (fun j => (gs j)⁻¹) [z] = (wordIn k gs [z])⁻¹ := by
  unfold wordIn
  cases h : toLetters k [z] with
  | nil => simp
  | cons a t =>
    have ht : t = [] := by
      have hl : (toLetters k [z]).length ≤ 1 := by
        unfold toLetters
        exact (List.length_filterMap_le _ _).trans (by simp)
      rw [h, List.length_cons] at hl
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst ht
    obtain ⟨j, b⟩ := a
    cases b <;> simp

theorem lpt_inv_eq {k : Nat} {S SI : Nat → Nat} {gs : Nat → Equiv.Perm (Fin 1755)}
    (hS : ∀ j < k, PR (S j) (gs j)) (hSI : ∀ j < k, PR (SI j) (gs j)⁻¹) {z : Int}
    (hl : lettersK k [z] = true) (x : Fin 1755) :
    lpt SI S z x = ((wordIn k gs [z])⁻¹ x : Nat) := by
  have hS' : ∀ j < k, PR (SI j) ((fun j => (gs j)⁻¹) j) := hSI
  have hSI' : ∀ j < k, PR (S j) ((fun j => (gs j)⁻¹) j)⁻¹ := fun j hj => by
    simpa using hS j hj
  have := wpt_eq hS' hSI' hl x
  rw [wordIn_single_inv] at this
  exact this

theorem lettersK_cons_iff {k : Nat} {z : Int} {w : List Int} :
    lettersK k (z :: w) = true ↔ lettersK k [z] = true ∧ lettersK k w = true := by
  rw [lettersK_cons, lettersK_cons]
  simp [lettersK]

theorem wipt_eq {k : Nat} {S SI : Nat → Nat} {gs : Nat → Equiv.Perm (Fin 1755)}
    (hS : ∀ j < k, PR (S j) (gs j)) (hSI : ∀ j < k, PR (SI j) (gs j)⁻¹) :
    ∀ {w : List Int}, lettersK k w = true → ∀ x : Fin 1755,
      wipt S SI w x = ((wordIn k gs w)⁻¹ x : Nat)
  | [], _, x => by
    change (x : Nat) = _
    simp [wordIn, toLetters]
  | z :: w, hl, x => by
    obtain ⟨h1, h2⟩ := lettersK_cons_iff.1 hl
    change wipt S SI w (lpt SI S z x) = _
    rw [lpt_inv_eq hS hSI h1 x]
    have e : ((wordIn k gs [z])⁻¹ x : Nat) = (((wordIn k gs [z])⁻¹ x : Fin 1755) : Nat) := rfl
    rw [e, wipt_eq hS hSI h2]
    have hw : wordIn k gs (z :: w) = wordIn k gs [z] * wordIn k gs w := by
      rw [← wordIn_append]
      rfl
    rw [hw, mul_inv_rev, Equiv.Perm.mul_apply]

end CFSG.KD.T49

end
