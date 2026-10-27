module

public import Certificates.Data.Kernel.Fi22.Letters
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.Fi22L

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native
  CFSG.Perm.Native CFSG.F3.Native

variable {P S : Nat}

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem orbList_length (t : Nat) : ∀ c j, (orbList t j c).length = c
  | 0, _ => rfl
  | c + 1, j => by simp [orbList, orbList_length t c]

theorem orbList_getElem (t : Nat) : ∀ c j i (h : i < (orbList t j c).length),
    (orbList t j c)[i] = UInt32.ofNat (orbEntry t (j + i))
  | 0, _, i, h => by simp [orbList] at h
  | c + 1, j, 0, _ => by simp [orbList]
  | c + 1, j, i + 1, h => by
    simp only [orbList, List.getElem_cons_succ]
    rw [orbList_getElem t c (j + 1) i]
    congr 2
    omega

theorem orbTab_size (t : Nat) : (orbTab t).size = 3510 := by
  simp [orbTab, orbList_length]

theorem ap_orbTab {t y : Nat} (hy : y < 3510) : ap (orbTab t) y = orbEntry t y := by
  have hs : y < (orbTab t).size := by rw [orbTab_size]; exact hy
  unfold ap
  rw [getElem!_pos _ y hs]
  have e : (orbTab t)[y]'hs = UInt32.ofNat (orbEntry t (0 + y)) :=
    orbList_getElem t 3510 0 y (by rw [orbList_length]; exact hy)
  rw [e, Nat.zero_add, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))

theorem wM_eq (m : Nat) : wM m = 2 ^ m - 1 := by
  unfold wM
  change (1 <<< m) - 1 = 2 ^ m - 1
  rw [Nat.one_shiftLeft]

theorem fld_window (P s y m : Nat) (hy : 12 * y + 12 ≤ m) :
    Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight P s) (wM m)) (Nat.mul 12 y)) 4095 =
      (P >>> (s + 12 * y)) % 4096 := by
  change ((P >>> s) &&& wM m) >>> (12 * y) &&& (2 ^ 12 - 1) = (P >>> (s + 12 * y)) % 2 ^ 12
  rw [wM_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < 12
  · have h2 : 12 * y + i < m := by omega
    simp only [hi, h2, decide_true, Bool.true_and]
    congr 1
    omega
  · simp [hi]

theorem regT_lt {t : Nat} (ht : t < 2) : regT P t = orbT t := by
  unfold regT
  have h : Nat.blt t 2 = true := Nat.blt_eq.mpr ht
  rw [h]

theorem regT_three : regT P 3 = orbT 0 := rfl

theorem reg_orbL {t y : Nat} (ht : t < 2) (hy : y < 3510) : reg P t y = orbEntry t y := by
  unfold reg lk
  rw [regT_lt ht]
  unfold orbT tM
  rw [fld_window orbPacked _ y (nat_lit 42120) (by change 12 * y + 12 ≤ 42120; omega)]
  unfold orbEntry
  congr 2
  change 42120 * t + 12 * y = 12 * (3510 * t + y)
  omega

theorem reg_three (y : Nat) : reg P 3 y = reg P 0 y := by
  unfold reg
  rw [regT_three, regT_lt (by norm_num)]

theorem TR_congr {n : Nat} {t : Table} {f g : Nat → Nat} (h : TR n t f) (hfg : ∀ i < n, f i = g i) :
    TR n t g :=
  ⟨h.1, fun i hi => by rw [← hfg i hi]; exact h.2 i hi⟩

theorem gen_facts (hg : genChkK P = true) {y : Nat} (hy : y < 3510) :
    reg P 0 y < 3510 ∧ reg P 1 y < 3510 ∧ reg P 2 y < 3510 ∧ reg P 2 (reg P 1 y) = y ∧ reg P 1 (reg P 2 y) = y := by
  have h := allN_spec hg y hy
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem tr_alpha (hg : genChkK P = true) : TR 3510 orbL.alpha (reg P 0) :=
  ⟨orbTab_size 0, fun i hi => ⟨by
    rw [reg_orbL (by norm_num) hi]
    exact ap_orbTab hi, (gen_facts hg hi).1⟩⟩

theorem tr_beta (hg : genChkK P = true) : TR 3510 orbL.beta (reg P 1) :=
  ⟨orbTab_size 1, fun i hi => ⟨by
    rw [reg_orbL (by norm_num) hi]
    exact ap_orbTab hi, (gen_facts hg hi).2.1⟩⟩

theorem tr_binv (hg : genChkK P = true) : TR 3510 (invT 3510 orbL.beta) (reg P 2) :=
  invT_TR (by norm_num) (tr_beta hg) fun i hi =>
    ⟨(gen_facts hg hi).2.2.1, (gen_facts hg hi).2.2.2.2, (gen_facts hg hi).2.2.2.1⟩

@[expose] noncomputable def gz (P : Nat) (z : Int) : Nat → Nat :=
  if z = 1 ∨ z = -1 then reg P 0 else if z = 2 then reg P 1 else reg P 2

theorem tr_gen (hg : genChkK P = true) (z : Int) : TR 3510 (genTables orbL z) (gz P z) := by
  unfold genTables gz
  by_cases h1 : z = 1 ∨ z = -1
  · simp only [h1, ↓reduceIte]
    exact tr_alpha hg
  by_cases h2 : z = 2
  · simp only [h2, ↓reduceIte]
    exact tr_beta hg
  · simp only [h1, h2, ↓reduceIte]
    exact tr_binv hg

theorem gz_chOf {c : Nat} (hc : c < 4) (y : Nat) : gz P (letterOf (chOf c)) y = reg P c y := by
  interval_cases c
  · rfl
  · rfl
  · rfl
  · rw [reg_three]
    rfl

theorem exF_zero (k : Nat) : exF S 0 k = [k] := rfl

theorem exF_succ (f k : Nat) : exF S (f + 1) k =
    Bool.rec (motive := fun _ => List Nat) (List.append (exF S f (raOf S k)) (exF S f (rbOf S k))) [k]
      (Nat.blt k 4) := rfl

theorem rule_facts {k : Nat} (h : ruleChkK P S k = true) :
    raOf S k < k ∧ rbOf S k < k ∧ ∀ x < 3510, reg P k x = reg P (raOf S k) (reg P (rbOf S k) x) := by
  unfold ruleChkK at h
  rw [strictB_eq, strictB_eq] at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun x hx => Nat.eq_of_beq_eq_true (allN_spec h3 x hx)⟩

theorem gen_lt (hg : genChkK P = true) {k y : Nat} (hk : k < 4) (hy : y < 3510) : reg P k y < 3510 := by
  have hf := gen_facts hg hy
  interval_cases k
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2.1
  · rw [reg_three]
    exact hf.1

theorem slp_spec (hg : genChkK P = true) (hr : ∀ k, 4 ≤ k → k < 137 → ruleChkK P S k = true) :
    ∀ f k, k ≤ f → k < 137 → ∀ x < 3510,
      reg P k x < 3510 ∧ (exF S f k).foldr (fun c y => gz P (letterOf (chOf c)) y) x = reg P k x
  | 0, k, hk, _, x, hx => by
    have : k = 0 := by omega
    subst this
    exact ⟨gen_lt hg (by norm_num) hx, gz_chOf (by norm_num) x⟩
  | f + 1, k, hk, hk', x, hx => by
    rw [exF_succ]
    by_cases h4 : k < 4
    · have e : Nat.blt k 4 = true := Nat.blt_eq.mpr h4
      rw [e]
      exact ⟨gen_lt hg h4 hx, gz_chOf h4 x⟩
    · have e : Nat.blt k 4 = false := by
        rw [Bool.eq_false_iff]
        intro h
        exact h4 (Nat.blt_eq.mp h)
      rw [e]
      obtain ⟨ha, hb, hk3⟩ := rule_facts (hr k (by omega) hk')
      have ihb := slp_spec hg hr f (rbOf S k) (by omega) (by omega) x hx
      have iha := slp_spec hg hr f (raOf S k) (by omega) (by omega) (reg P (rbOf S k) x) ihb.1
      refine ⟨by rw [hk3 x hx]; exact iha.1, ?_⟩
      change (exF S f (raOf S k) ++ exF S f (rbOf S k)).foldr _ x = reg P k x
      rw [List.foldr_append, ihb.2, iha.2, hk3 x hx]

theorem word_facts (hg : genChkK P = true) (hr : ∀ k, 4 ≤ k → k < 137 → ruleChkK P S k = true)
    (hwr : wrChkK S = true)
    (hw : ∀ j < 16, (chainWords ())[j]! = ((exF S 136 (wrOf S j)).map chOf).map letterOf) :
    ∀ j < 16, TR 3510 (wordT 3510 (genTables orbL) (chainWords ())[j]!) (reg P (wrOf S j)) := by
  intro j hj
  have hT := wordT_TR (n := 3510) (by norm_num) (gens := genTables orbL)
    (G := gz P) (chainWords ())[j]! fun z _ => tr_gen hg z
  refine TR_congr hT fun x hx => ?_
  have hwj : wrOf S j < 137 := Nat.blt_eq.mp (allN_spec hwr j hj)
  have hf := slp_spec hg hr 136 (wrOf S j) (by omega) hwj x hx
  rw [← hf.2, hw j hj, List.foldr_map, List.foldr_map]

theorem LJk_eq (l x : Nat) :
    LJk P S l x = if l % 2 = 0 then reg P (wrOf S (l / 2)) x else invL P (l / 2) x := by
  have e1 : Nat.land l 1 = l % 2 := Nat.and_one_is_mod l
  have e2 : Nat.shiftRight l 1 = l / 2 := by
    change l >>> 1 = l / 2
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
  unfold LJk
  rw [e1, e2]
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

theorem inv_facts {j : Nat} (h : invChkK P S j = true) {x : Nat} (hx : x < 3510) :
    invL P j x < 3510 ∧ invL P j (reg P (wrOf S j) x) = x ∧ reg P (wrOf S j) (invL P j x) = x := by
  unfold invChkK at h
  rw [strictB_eq] at h
  have h' := allN_spec h x hx
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h'
  exact h'

@[expose] noncomputable def LJA (P S : Nat) : Array Table :=
  Array.ofFn (n := 32) fun l => Array.ofFn (n := 3510) fun x => UInt32.ofNat (LJk P S l.val x.val)

theorem TR_ext {n : Nat} {t u : Table} {f : Nat → Nat} (ht : TR n t f) (hu : TR n u f) : t = u := by
  apply Array.ext (by rw [ht.1, hu.1])
  intro i hi1 hi2
  have hi : i < n := by rw [← ht.1]; exact hi1
  have e1 := (ht.2 i hi).1
  have e2 := (hu.2 i hi).1
  unfold ap at e1 e2
  rw [getElem!_pos _ i hi1] at e1
  rw [getElem!_pos _ i hi2] at e2
  exact UInt32.toNat_inj.mp (e1.trans e2.symm)

theorem LJA_size : (LJA P S).size = 32 := by
  unfold LJA
  rw [Array.size_ofFn]

theorem LJA_get {l : Nat} (hl : l < 32) : (LJA P S)[l]'(by rw [LJA_size]; exact hl) =
    Array.ofFn (n := 3510) fun x => UInt32.ofNat (LJk P S l x.val) := by
  simp only [LJA, Array.getElem_ofFn]

theorem LJA_TR {l : Nat} (hl : l < 32) (hv : ∀ x < 3510, LJk P S l x < 3510) :
    TR 3510 ((LJA P S)[l]'(by rw [LJA_size]; exact hl)) (LJk P S l) := by
  rw [LJA_get hl]
  refine ⟨by rw [Array.size_ofFn], fun x hx => ⟨?_, hv x hx⟩⟩
  unfold ap
  rw [getElem!_pos _ x (by rw [Array.size_ofFn]; exact hx), Array.getElem_ofFn, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_trans (hv x hx) (by norm_num))

theorem arr_eq {m : Nat} {A B : Array Table} {F : Nat → Nat → Nat} (hA : A.size = m) (hB : B.size = m)
    (htA : ∀ l < m, TR 3510 A[l]! (F l)) (htB : ∀ l (h : l < m), TR 3510 (B[l]'(hB ▸ h)) (F l)) :
    A = B := by
  refine Array.ext (hA.trans hB.symm) fun l h1 h2 => ?_
  have hl : l < m := by rw [← hA]; exact h1
  have e := TR_ext (htA l hl) (htB l hl)
  rwa [getElem!_pos _ l h1] at e

theorem letters_sound (hg : genChkK P = true) (hr : ∀ k, 4 ≤ k → k < 137 → ruleChkK P S k = true)
    (hi : ∀ j < 16, invChkK P S j = true) (hwr : wrChkK S = true) (hs : (chainWords ()).size = 16)
    (hw : ∀ j < 16, (chainWords ())[j]! = ((exF S 136 (wrOf S j)).map chOf).map letterOf) :
    (chainLetters orbL).size = 32 ∧ (∀ l < 32, TR 3510 (chainLetters orbL)[l]! (LJk P S l)) ∧
      chainLetters orbL = LJA P S := by
  have hwj := word_facts hg hr hwr hw
  have e : chainLetters orbL = buildLetters 3510 (genTables orbL) (chainWords ()) := rfl
  have hsz : (chainLetters orbL).size = 32 := by
    rw [e]
    unfold buildLetters
    rw [Array.size_ofFn, hs]
  have htr : ∀ l < 32, TR 3510 (chainLetters orbL)[l]! (LJk P S l) := by
    intro l hl
    have hl' : l < (chainLetters orbL).size := by rw [hsz]; exact hl
    have hget : (chainLetters orbL)[l]! =
        if l % 2 = 0 then wordT 3510 (genTables orbL) (chainWords ())[l / 2]!
        else invT 3510 (wordT 3510 (genTables orbL) (chainWords ())[l / 2]!) := by
      rw [getElem!_pos _ l hl']
      simp only [e, buildLetters, Array.getElem_ofFn]
    have hj : l / 2 < 16 := by omega
    rw [hget]
    by_cases hev : l % 2 = 0
    · simp only [hev, ↓reduceIte]
      exact TR_congr (hwj (l / 2) hj) fun x _ => by simp only [LJk_eq, hev, ↓reduceIte]
    · simp only [hev, ↓reduceIte]
      have hf := hwj (l / 2) hj
      have hT := invT_TR (by norm_num) hf (g := invL P (l / 2)) fun x hx =>
        ⟨(inv_facts (hi _ hj) hx).1, (inv_facts (hi _ hj) hx).2.2, (inv_facts (hi _ hj) hx).2.1⟩
      exact TR_congr hT fun x _ => by simp only [LJk_eq, hev, ↓reduceIte]
  exact ⟨hsz, htr, arr_eq hsz LJA_size htr fun l hl => LJA_TR hl fun x hx => ((htr l hl).2 x hx).2⟩

end CFSG.KS.Fi22L

end
