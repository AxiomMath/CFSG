
module

public import Certificates.Data.Kernel.SporSch.J4SCols
public import CFSG.Sporadic.Schreier.J4SKCentBase
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.PairText
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.SporSch.C11

open CFSG.KC.Enum CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native
open CFSG.Sporadic.Schreier.PairText

@[expose] noncomputable def unpackW (w m P : Nat) : Array Nat :=
  Array.ofFn (n := m) fun i => ent w P i.val

@[expose] noncomputable def unpack11 (P : Nat) : Array Nat := unpackW 11 11 P

theorem unpackW_get {w m P i : Nat} (hi : i < m) : (unpackW w m P)[i]! = ent w P i := by
  rw [unpackW, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem unpack11_bounded (P : Nat) :
    (unpack11 P).size = 11 ∧ ∀ j < 11, (unpack11 P)[j]! < 2048 := by
  refine ⟨by simp [unpack11, unpackW], fun j hj => ?_⟩
  rw [unpack11, unpackW_get hj, ent]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem ent_pg (w P i : Nat) : ent w P i = pg w (mask w) P i := rfl

private theorem colK_ent (P j : Nat) : colK P j = ent 11 P j := rfl

private theorem ent_lt (w P i : Nat) : ent w P i < 2 ^ w := by
  rw [ent_pg]
  exact PackFld.pg_lt w P i

private theorem unpackW_getD {w m P j : Nat} (hj : j < m) :
    (unpackW w m P)[j]?.getD 0 = ent w P j := by
  simp [unpackW, hj]

private theorem bit_beq (a j : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight a j) (nat_lit 1)) (nat_lit 1) = a.testBit j := by
  have e : Nat.land (Nat.shiftRight a j) 1 = a / 2 ^ j % 2 := by
    change (a >>> j) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  exact Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, decide_eq_true_iff])

private theorem app_rec (P a : Nat) : ∀ n, n ≤ 11 →
    (List.range n).foldl
      (fun acc j => if a.testBit j then acc ^^^ ((unpack11 P)[j]?.getD 0) else acc) 0 =
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a j) (nat_lit 1))
        (nat_lit 1), Nat.xor s (colK P j), s))) n
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.foldl_append, app_rec P a n (by omega)]
    change _ = strictN _ _
    rw [sN, nIf_eq, bit_beq, List.foldl_cons, List.foldl_nil, unpack11, unpackW_getD (by omega),
      colK_ent]
    rfl

private theorem app_eq' (P a : Nat) : app11 (unpack11 P) a = appK P a := by
  unfold app11 vecMulN
  exact app_rec P a 11 le_rfl

private theorem appK_lt (P a : Nat) : appK P a < 2 ^ 11 := by
  suffices h : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a j) (nat_lit 1))
        (nat_lit 1), Nat.xor s (colK P j), s))) n < 2 ^ 11 from h 11
  intro n
  induction n with
  | zero => exact Nat.two_pow_pos 11
  | succ n ih =>
    change strictN _ _ < _
    rw [sN, nIf_eq]
    split
    · exact Nat.xor_lt_two_pow ih (by rw [colK_ent]; exact ent_lt _ _ _)
    · exact ih

private theorem fld_packR (f : Nat → Nat) (hf : ∀ j, j < 11 → f j < 2 ^ 11) : ∀ n, n ≤ 11 →
    PackFld.Fld 11 (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc (fun s => Nat.lor s (Nat.shiftLeft (f j) (Nat.mul (nat_lit 11) j))))
      n) (fun i => if i < n then f i else 0)
  | 0, _ => PackFld.fld_congr (PackFld.fld_zero 11) (fun i => by simp)
  | n + 1, h => by
    change PackFld.Fld 11 (strictN _ _) _
    rw [sN]
    refine PackFld.fld_congr (PackFld.fld_or (fld_packR f hf n (by omega))
      (PackFld.fld_shl n (PackFld.fld_one (hf n (by omega))))) (fun i => ?_)
    by_cases h1 : i < n
    · have h2 : ¬ n ≤ i := by omega
      simp [h1, h2, show i < n + 1 by omega]
    · by_cases h3 : i = n
      · subst h3
        simp
      · have h4 : ¬ i < n + 1 := by omega
        have h5 : i - n ≠ 0 := by omega
        simp [h1, h4, h5]

private theorem unpack11_packK (f : Nat → Nat) (hf : ∀ j, j < 11 → f j < 2 ^ 11) :
    unpack11 (packK f) = Array.ofFn (n := 11) fun j => f j.val := by
  refine Array.ext (by simp [unpack11, unpackW]) (fun j h1 h2 => ?_)
  have hj : j < 11 := by simpa [unpack11, unpackW] using h1
  simp only [unpack11, unpackW, Array.getElem_ofFn]
  rw [ent_pg]
  have := PackFld.pg_of_fld (fld_packR f hf 11 le_rfl) (i := j) (by simpa [hj] using hf j hj)
  simp only [hj, ↓reduceIte] at this
  exact this

private noncomputable def packL (w : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, j => x <<< (w * j) ||| packL w xs (j + 1)

private theorem bindW_rec {w m P : Nat} : ∀ (l : List Nat) (j acc : Nat),
    List.rec (motive := fun _ => Nat → Nat → Bool)
      (fun j acc => bAnd(Nat.beq j m, Nat.beq acc P))
      (fun x _ ih j acc => bAnd(Nat.blt x (Nat.shiftLeft (nat_lit 1) w),
        strictB (Nat.lor acc (Nat.shiftLeft x (Nat.mul w j))) (fun acc' =>
          ih (Nat.succ j) acc'))) l j acc = true →
    (∀ x ∈ l, x < 2 ^ w) ∧ j + l.length = m ∧ P = acc ||| packL w l j
  | [], j, acc, h => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    refine ⟨by simp, by simpa using Nat.eq_of_beq_eq_true h1, ?_⟩
    rw [packL, Nat.or_zero, Nat.eq_of_beq_eq_true h2]
  | x :: xs, j, acc, h => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    rw [sB] at h2
    obtain ⟨ha, hb, hc⟩ := bindW_rec xs _ _ h2
    have hx : x < 2 ^ w := by
      have := Nat.blt_eq.mp h1
      rwa [PackFld.shl_eq, Nat.one_mul] at this
    refine ⟨?_, by simp only [List.length_cons] at hb ⊢; omega, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact ha y hy
    · rw [hc, packL, ← Nat.or_assoc]
      rfl

private theorem fld_packL {w : Nat} : ∀ (l : List Nat) (j : Nat), (∀ x ∈ l, x < 2 ^ w) →
    PackFld.Fld w (packL w l j) (fun i => if j ≤ i then l[i - j]?.getD 0 else 0)
  | [], j, _ => PackFld.fld_congr (PackFld.fld_zero w) (fun i => by simp)
  | x :: xs, j, h => by
    refine PackFld.fld_congr (PackFld.fld_or (PackFld.fld_shl j (PackFld.fld_one
      (h x (List.mem_cons_self ..)))) (fld_packL xs (j + 1) (fun y hy => h y
        (List.mem_cons_of_mem _ hy)))) (fun i => ?_)
    by_cases h1 : j ≤ i
    · by_cases h3 : i = j
      · subst h3
        simp
      · have h4 : i - j = (i - (j + 1)) + 1 := by omega
        simp [h1, show j + 1 ≤ i by omega, h4]
    · simp [h1, show ¬ j + 1 ≤ i by omega]

theorem bindW_sound {w m P : Nat} {a : Array Nat} (h : bindWK w m a.toList P = true) :
    a = unpackW w m P := by
  obtain ⟨ha, hb, hc⟩ := bindW_rec a.toList 0 0 h
  rw [Nat.zero_or] at hc
  subst hc
  have hs : a.size = m := by simpa using hb
  refine Array.ext (by simp [unpackW, hs]) (fun i h1 h2 => ?_)
  simp only [unpackW, Array.getElem_ofFn]
  rw [ent_pg, PackFld.pg_of_fld (fld_packL a.toList 0 ha) ?_]
  · simp [h1]
  · have := ha (a.toList[i]'(by simpa using h1)) (List.getElem_mem _)
    simpa [h1] using this

private theorem bind2_rec {w m n : Nat} {T : Nat → Nat} : ∀ (L : List (Array Nat)) (k : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k n)
      (fun a _ ih k => bAnd(bindWK w m a.toList (T k), ih (Nat.succ k))) L k = true →
    k + L.length = n ∧ ∀ i (hi : i < L.length), L[i] = unpackW w m (T (k + i))
  | [], k, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun i hi => absurd hi (by simp)⟩
  | a :: L, k, h => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    obtain ⟨hb, hc⟩ := bind2_rec L (k + 1) h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    rcases i with _ | i
    · exact bindW_sound h1
    · rw [List.getElem_cons_succ, hc i (by simpa using hi)]
      congr 2
      omega

theorem bind2_sound {w m n : Nat} {T : Nat → Nat} {A : Array (Array Nat)}
    (h : bind2K w m A.toList T n = true) :
    A.size = n ∧ ∀ k < n, A[k]! = unpackW w m (T k) := by
  obtain ⟨hb, hc⟩ := bind2_rec A.toList 0 h
  have hs : A.size = n := by simpa using hb
  refine ⟨hs, fun k hk => ?_⟩
  rw [getElem!_pos A k (by omega), ← Array.getElem_toList, hc k (by simpa [hs] using hk),
    Nat.zero_add]

theorem comp_sound {P Q R : Nat} (h : Nat.beq (compK P Q) R = true) :
    comp11 (unpack11 P) (unpack11 Q) = unpack11 R := by
  rw [← Nat.eq_of_beq_eq_true h, compK, unpack11_packK _ (fun j _ => appK_lt P _)]
  refine Array.ext (by simp [comp11, mulRows, unpack11, unpackW]) (fun j h1 h2 => ?_)
  have hj : j < 11 := by simpa using h2
  simp only [comp11, mulRows, Array.getElem_map, Array.getElem_ofFn]
  rw [← app_eq', colK_ent]
  simp [unpack11, unpackW]

theorem id_sound {R : Nat} (h : Nat.beq pidK R = true) : idRows 11 = unpack11 R := by
  have hf : ∀ j, j < 11 → Nat.shiftLeft (nat_lit 1) j < 2 ^ 11 := fun j hj => by
    rw [PackFld.shl_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by decide) hj
  rw [← Nat.eq_of_beq_eq_true h, pidK, unpack11_packK _ hf]
  rfl

private theorem eq_of_unpack {P Q : Nat} (hP : canonK P = true) (hQ : canonK Q = true)
    (e : unpack11 P = unpack11 Q) : P = Q := by
  have hf : ∀ j < 11, ent 11 P j = ent 11 Q j := fun j hj => by
    rw [← unpackW_get (m := 11) hj, ← unpackW_get (m := 11) hj]
    exact congrArg (·[j]!) e
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 121
  · have hd := Nat.div_add_mod k 11
    have hj : k / 11 < 11 := by omega
    have t := congrArg (fun x => x.testBit (k % 11)) (hf _ hj)
    simp only [ent_pg, PackFld.testBit_pgM, hd, Nat.mod_lt k (by decide : 11 > 0), decide_true,
      Bool.true_and] at t
    exact t
  · have e1 : k = 121 + (k - 121) := by omega
    have eP : P >>> 121 = 0 := Nat.eq_of_beq_eq_true hP
    have eQ : Q >>> 121 = 0 := Nat.eq_of_beq_eq_true hQ
    rw [e1, ← Nat.testBit_shiftRight, ← Nat.testBit_shiftRight, eP, eQ]

theorem ne_sound {P Q : Nat} (h : bAnd(canonK P, bAnd(canonK Q, Bool.not (Nat.beq P Q))) = true) :
    unpack11 P ≠ unpack11 Q := by
  obtain ⟨hP, h⟩ := bAnd_true h
  obtain ⟨hQ, h⟩ := bAnd_true h
  intro e
  rw [eq_of_unpack hP hQ e, Nat.beq_refl] at h
  exact Bool.noConfusion h

private theorem foldBlk_add {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i s, f i s = s + g i)
    (b : Nat) : ∀ len s, foldBlk b f len s = s + ∑ l ∈ Finset.range len, g (b + l)
  | 0, s => by simp [foldBlk]
  | len + 1, s => by
    change strictN (f (Nat.add b len) s) (foldBlk b f len) = _
    rw [sN, foldBlk_add hf b len, hf, Finset.sum_range_succ]
    simp only [Nat.add_eq]
    ring

private theorem foldN_add {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i s, f i s = s + g i)
    (n s : Nat) : foldN n f s = s + ∑ i ∈ Finset.range n, g i := by
  have sl : ∀ a, Nat.shiftLeft a (nat_lit 6) = 64 * a := fun a => by
    rw [Nat.mul_comm]
    exact Nat.shiftLeft_eq a 6
  have key : ∀ q s', Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) q s' =
      s' + ∑ i ∈ Finset.range (64 * q), g i := by
    intro q
    induction q with
    | zero => intro s'; simp
    | succ h ih =>
      intro s'
      change strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s') _ = _
      rw [sN, ih, foldBlk_add hf, Nat.mul_succ, Finset.sum_range_add, sl]
      ring
  have e1 : Nat.land n (nat_lit 63) = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6
  have e2 : Nat.shiftRight n (nat_lit 6) = n / 64 := Nat.shiftRight_eq_div_pow n 6
  unfold foldN
  dsimp only
  rw [key, foldBlk_add hf, e1, e2, sl]
  conv_rhs => rw [← Nat.div_add_mod n 64, Finset.sum_range_add]
  ring

theorem fix_sound {P c : Nat} (h : Nat.beq (fixCntK P) c = true) : fixCount (unpack11 P) = c := by
  rw [← Nat.eq_of_beq_eq_true h, fixCount, fixCntK,
    foldN_add (g := fun a => if appK P a = a then 1 else 0), Nat.zero_add, Finset.card_filter]
  · simp only [app_eq']
  · intro i s
    rw [nIf_eq]
    by_cases e : appK P i = i <;> simp [e, Nat.beq_eq]

theorem fixLe_sound {P b : Nat} (h : Nat.ble (fixCntK P) b = true) :
    fixCount (unpack11 P) ≤ b := by
  rw [fix_sound (Nat.beq_refl _)]
  exact Nat.le_of_ble_eq_true h

private theorem letK_lt (X XI Y YI : Nat) (l : Int) {a : Nat} (ha : a < 2 ^ 11) :
    letK X XI Y YI l a < 2 ^ 11 := by
  cases l with
  | ofNat k =>
    change Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) a (appK Y a)
      (Nat.beq k 2)) (appK X a) (Nat.beq k 1) < _
    rw [nIf_eq, nIf_eq]
    split_ifs
    · exact appK_lt _ _
    · exact appK_lt _ _
    · exact ha
  | negSucc k =>
    change Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) a (appK YI a)
      (Nat.beq k 1)) (appK XI a) (Nat.beq k 0) < _
    rw [nIf_eq, nIf_eq]
    split_ifs
    · exact appK_lt _ _
    · exact appK_lt _ _
    · exact ha

private theorem letK_eq {X XI Y YI : Nat} (hX : xColumns = unpack11 X)
    (hXI : xInvColumns = unpack11 XI) (hY : yColumns = unpack11 Y)
    (hYI : yInvColumns = unpack11 YI) (l : Int) (a : Nat) :
    letterApp l a = letK X XI Y YI l a := by
  cases l with
  | ofNat k =>
    change _ = Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) a (appK Y a)
      (Nat.beq k 2)) (appK X a) (Nat.beq k 1)
    rw [nIf_eq, nIf_eq]
    have n1 : ¬ ((k : ℤ) = -1) := by omega
    have n2 : ¬ ((k : ℤ) = -2) := by omega
    simp only [letterApp, Nat.beq_eq, ← app_eq', ← hX, ← hY, Int.ofNat_eq_natCast, n1, n2,
      ite_false]
    split_ifs <;> first | rfl | omega
  | negSucc k =>
    change _ = Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) a (appK YI a)
      (Nat.beq k 1)) (appK XI a) (Nat.beq k 0)
    rw [nIf_eq, nIf_eq]
    simp only [letterApp, Nat.beq_eq, ← app_eq', ← hXI, ← hYI]
    simp only [Int.negSucc_eq]
    split_ifs <;> first | rfl | omega

private theorem wordAppK_eq {X XI Y YI : Nat} (hX : xColumns = unpack11 X)
    (hXI : xInvColumns = unpack11 XI) (hY : yColumns = unpack11 Y)
    (hYI : yInvColumns = unpack11 YI) : ∀ (w : List Int) (a : Nat), a < 2 ^ 11 →
    app11W w a = wordAppK X XI Y YI w a ∧ wordAppK X XI Y YI w a < 2 ^ 11
  | [], a, ha => ⟨rfl, ha⟩
  | l :: w, a, ha => by
    obtain ⟨e, hl⟩ := wordAppK_eq hX hXI hY hYI w a ha
    change letterApp l (app11W w a) = strictN (wordAppK X XI Y YI w a) (fun b => letK X XI Y YI l b)
      ∧ strictN (wordAppK X XI Y YI w a) (fun b => letK X XI Y YI l b) < _
    rw [sN, e, letK_eq hX hXI hY hYI]
    exact ⟨rfl, letK_lt _ _ _ _ _ hl⟩

theorem wordCols_sound {X XI Y YI P : Nat} {w : List Int}
    (hX : bindWK 11 11 xColumns.toList X = true) (hXI : bindWK 11 11 xInvColumns.toList XI = true)
    (hY : bindWK 11 11 yColumns.toList Y = true) (hYI : bindWK 11 11 yInvColumns.toList YI = true)
    (h : Nat.beq (wordColsK X XI Y YI w) P = true) : wordCols w = unpack11 P := by
  have E := wordAppK_eq (bindW_sound hX) (bindW_sound hXI) (bindW_sound hY) (bindW_sound hYI) w
  have hs : ∀ j, j < 11 → Nat.shiftLeft (nat_lit 1) j < 2 ^ 11 := fun j hj => by
    rw [PackFld.shl_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by decide) hj
  rw [← Nat.eq_of_beq_eq_true h, wordColsK, unpack11_packK _ (fun j hj => (E _ (hs j hj)).2)]
  unfold wordCols
  congr 1
  funext j
  have e : Nat.shiftLeft (nat_lit 1) j.val = 2 ^ j.val := by rw [PackFld.shl_eq, Nat.one_mul]
  rw [e]
  exact (E _ (by rw [← e]; exact hs j j.isLt)).1

private def stepW (t : Array Int) (b : Nat × Array (List Int)) (_ : Nat) : Nat × Array (List Int) :=
  ((tokWord t b.1).2, b.2.push (tokWord t b.1).1)

private theorem tokWords_eq (t : Array Int) (i k : Nat) :
    tokWords t i k = ((List.range' 0 k).foldl (stepW t) (i, #[])).swap := by
  simp only [tokWords, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero]
  rfl

private theorem icode_inj {x y : Int} (h : intEqK x y = true) : x = y := by
  have e : CFSG.KS.Mathieu.icode x = CFSG.KS.Mathieu.icode y := Nat.eq_of_beq_eq_true h
  cases x with
  | ofNat a =>
    cases y with
    | ofNat b =>
      change Nat.add a a = Nat.add b b at e
      simp only [Nat.add_eq] at e
      congr 1
      omega
    | negSucc b =>
      change Nat.add a a = Nat.succ (Nat.add (Nat.succ b) (Nat.succ b)) at e
      simp only [Nat.add_eq, Nat.succ_eq_add_one] at e
      omega
  | negSucc a =>
    cases y with
    | ofNat b =>
      change Nat.succ (Nat.add (Nat.succ a) (Nat.succ a)) = Nat.add b b at e
      simp only [Nat.add_eq, Nat.succ_eq_add_one] at e
      omega
    | negSucc b =>
      change Nat.succ (Nat.add (Nat.succ a) (Nat.succ a)) =
        Nat.succ (Nat.add (Nat.succ b) (Nat.succ b)) at e
      simp only [Nat.add_eq, Nat.succ_eq_add_one] at e
      congr 1
      omega

private theorem seqK_sound {k : List Int → Bool} : ∀ (w ys : List Int), seqK w ys k = true →
    ∃ rest, ys = w ++ rest ∧ k rest = true
  | [], ys, h => ⟨ys, rfl, h⟩
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: w, y :: ys, h => by
    change bAnd(intEqK x y, seqK w ys k) = true at h
    obtain ⟨h1, h2⟩ := bAnd_true h
    obtain ⟨r, hr, hk⟩ := seqK_sound w ys h2
    rw [icode_inj h1] at *
    exact ⟨r, by rw [hr]; rfl, hk⟩

private theorem lenI_eq : ∀ w : List Int, lenI w = w.length
  | [] => rfl
  | _ :: w => congrArg Nat.succ (lenI_eq w)

private theorem get_drop {L : List Int} {pos j : Nat} {v : Int} (h : (L.drop pos)[j]? = some v) :
    L.toArray[pos + j]! = v := by
  rw [List.getElem?_drop] at h
  simp [getElem!_def, h]

private theorem tokRun (L : List Int) : ∀ (ws : List (List Int)) (pos s : Nat)
    (out : Array (List Int)), tokWordsK (L.drop pos) ws = true →
    ((List.range' s ws.length).foldl (stepW L.toArray) (pos, out)).2 = out ++ ws.toArray
  | [], _, _, _, _ => by simp
  | w :: ws, pos, s, out, h => by
    cases hL : L.drop pos with
    | nil =>
      rw [hL] at h
      exact absurd h Bool.false_ne_true
    | cons y ys =>
      rw [hL] at h
      change bAnd(intEqK y (Int.ofNat (lenI w)), seqK w ys (fun L => tokWordsK L ws)) = true at h
      obtain ⟨h1, h2⟩ := bAnd_true h
      obtain ⟨r, hr, hk⟩ := seqK_sound w ys h2
      have hy := icode_inj h1
      rw [lenI_eq] at hy
      have e0 : L.toArray[pos]! = y := by
        have := get_drop (j := 0) (by rw [hL]; rfl)
        simpa using this
      have tw : tokWord L.toArray pos = (w, pos + 1 + w.length) := by
        unfold tokWord
        rw [e0, hy]
        simp only [Int.ofNat_eq_natCast, Int.toNat_natCast, Prod.mk.injEq, and_true]
        apply List.ext_getElem (by simp)
        intro j h1 h2
        rw [List.getElem_map, List.getElem_range]
        have := get_drop (L := L) (pos := pos) (j := 1 + j) (v := w[j]) (by
          rw [hL, hr]
          simp [Nat.add_comm 1 j, List.getElem?_append_left h2])
        rw [← Nat.add_assoc] at this
        exact this
      have hr' : L.drop (pos + 1 + w.length) = r := by
        rw [Nat.add_assoc, ← List.drop_drop, hL, hr, Nat.add_comm 1 w.length, List.drop_succ_cons,
          List.drop_left]
      rw [List.length_cons, List.range'_succ, List.foldl_cons]
      have e1 : stepW L.toArray (pos, out) s = (pos + 1 + w.length, out.push w) := by
        change ((tokWord L.toArray pos).2, out.push (tokWord L.toArray pos).1) = _
        rw [tw]
      rw [e1, tokRun L ws _ _ _ (by rw [hr']; exact hk)]
      simp

theorem tokWords_sound {L : List Int} {ws : List (List Int)} (h : tokWordsK L ws = true) :
    (tokWords L.toArray 0 ws.length).1 = ws.toArray := by
  rw [tokWords_eq, Prod.fst_swap, tokRun L ws 0 0 #[] (by simpa using h)]
  simp

theorem app_sound {P a b : Nat} (h : Nat.beq (appK P a) b = true) : app11 (unpack11 P) a = b := by
  rw [app_eq', Nat.eq_of_beq_eq_true h]

theorem app_eq (P a : Nat) : app11 (unpack11 P) a = appK P a := app_sound (Nat.beq_refl _)

theorem comp_eq (P Q : Nat) : comp11 (unpack11 P) (unpack11 Q) = unpack11 (compK P Q) :=
  comp_sound (Nat.beq_refl _)

theorem id_eq : idRows 11 = unpack11 pidK := id_sound (Nat.beq_refl _)

theorem wordCols_eq {X XI Y YI : Nat}
    (hX : bindWK 11 11 xColumns.toList X = true) (hXI : bindWK 11 11 xInvColumns.toList XI = true)
    (hY : bindWK 11 11 yColumns.toList Y = true) (hYI : bindWK 11 11 yInvColumns.toList YI = true)
    (w : List Int) : wordCols w = unpack11 (wordColsK X XI Y YI w) :=
  wordCols_sound hX hXI hY hYI (Nat.beq_refl _)

end CFSG.KS.SporSch.C11

end
