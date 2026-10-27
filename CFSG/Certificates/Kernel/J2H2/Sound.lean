module

public import CFSG.Certificates.Kernel.J2H2.Chain
public import CFSG.Certificates.Kernel.J2H2.Bits

public section

namespace CFSG.KC.J2H2

open CFSG.KD.J2H2 CFSG.KC.Enum
open CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue.H2
open CFSG.RankThree.PartTwo.J2Residue.C4725 CFSG.RankThree.PartTwo.J2Residue.H2S

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem nth_eq_getD {α : Type} (d : α) : ∀ (L : List α) (i : ℕ), nth d L i = L.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => by simp [nth, nth_eq_getD d L i]

@[expose] noncomputable def lmL (LMP : ℕ) (lL : List (List ℕ)) (k0 : ℕ) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k 3)
    (fun row _ ih k => bAnd(listK 7 127 LMP row (Nat.mul 128 k) (Nat.add (Nat.mul 128 k) 128),
      ih (Nat.succ k))) lL k0

theorem lmL_spec {LMP : ℕ} : ∀ {lL : List (List ℕ)} {k0 : ℕ}, lmL LMP lL k0 = true →
    ∀ k < lL.length, ∀ b < 128, pg 7 127 LMP (128 * (k0 + k) + b) = (lL.getD k []).getD b 0
  | [], _, _ => fun k hk => absurd hk (Nat.not_lt_zero _)
  | row :: lL, k0, h => by
    change bAnd(listK 7 127 LMP row (Nat.mul 128 k0) (Nat.add (Nat.mul 128 k0) 128),
      lmL LMP lL (Nat.succ k0)) = true at h
    rw [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    intro k hk b hb
    cases k with
    | zero =>
      obtain ⟨e, hr⟩ := listK_spec h1
      have hl : row.length = 128 := by
        change 128 * k0 + row.length = 128 * k0 + 128 at e
        omega
      simpa using hr b (hl ▸ hb)
    | succ k =>
      have := lmL_spec h2 k (by simp only [List.length_cons] at hk; omega) b hb
      rw [List.getD_cons_succ, ← this]
      congr 2
      omega

theorem data_spec {GP PP LMP : ℕ} (hd : dataK GP PP LMP genT parT lT = true) :
    (∀ x < 128, pg 2 3 GP x = gen x) ∧ (∀ x < 128, pg 7 127 PP x = par x) ∧
      ∀ k < 3, ∀ b < 128, pg 7 127 LMP (128 * k + b) = lmul k b := by
  change bAnd(listK 2 3 GP genT 0 128, bAnd(listK 7 127 PP parT 0 128, lmL LMP lT 0)) = true at hd
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at hd
  obtain ⟨h1, h2, h3⟩ := hd
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun k hk b hb => ?_⟩
  · have := (listK_spec h1).2 x (by rw [genT_length]; exact hx)
    rw [Nat.zero_add] at this
    rw [this, gen, nth_eq_getD]
  · have := (listK_spec h2).2 x (by rw [parT_length]; exact hx)
    rw [Nat.zero_add] at this
    rw [this, par, nth_eq_getD]
  · have hl : lT.length = 3 := by decide
    have := lmL_spec h3 k (hl ▸ hk) b hb
    rw [Nat.zero_add] at this
    rw [this, lmul, nth_eq_getD, nth_eq_getD]

@[expose] noncomputable def bitZ (x b : ℕ) : ZMod 2 := if x.testBit b then 1 else 0

theorem bitZ_xor (x y b : ℕ) : bitZ (x ^^^ y) b = bitZ x b + bitZ y b := by
  simp only [bitZ, Nat.testBit_xor]
  cases x.testBit b <;> cases y.testBit b <;> decide

theorem fieldMul (w : ℕ) : ∀ (β x y : ℕ), (∀ γ, x / 2 ^ (w * γ) % 2 ^ w * y < 2 ^ w) →
    x * y / 2 ^ (w * β) % 2 ^ w = x / 2 ^ (w * β) % 2 ^ w * y := by
  intro β
  induction β with
  | zero =>
    intro x y h
    have h0 := h 0
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h0 ⊢
    have e : x * y = 2 ^ w * (x / 2 ^ w * y) + x % 2 ^ w * y := by
      rw [← Nat.mul_assoc, ← Nat.add_mul, Nat.div_add_mod]
    rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt h0]
  | succ β ih =>
    intro x y h
    have h0 := h 0
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h0
    have e : x * y = 2 ^ w * (x / 2 ^ w * y) + x % 2 ^ w * y := by
      rw [← Nat.mul_assoc, ← Nat.add_mul, Nat.div_add_mod]
    have hd : x * y / 2 ^ w = x / 2 ^ w * y := by
      rw [e, Nat.mul_add_div (Nat.two_pow_pos w), Nat.div_eq_of_lt h0, Nat.add_zero]
    have hp : ∀ γ, 2 ^ (w * (γ + 1)) = 2 ^ w * 2 ^ (w * γ) := fun γ => by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [hp, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hd]
    refine ih (x / 2 ^ w) y fun γ => ?_
    have := h (γ + 1)
    rwa [hp, ← Nat.div_div_eq_div_mul] at this

theorem testBit_field (x a w r : ℕ) (hr : r < w) :
    (x / 2 ^ a % 2 ^ w).testBit r = x.testBit (a + r) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm r a]
  simp [hr]

theorem testBit_repN (q : ℕ) : repN.testBit q = decide (q % 384 = 0 ∧ q / 384 < 128) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
      (fun _ ih => Nat.lor 1 (Nat.shiftLeft ih 384)) n : ℕ).testBit q =
      decide (q % 384 = 0 ∧ q / 384 < n) := by
    intro n
    induction n generalizing q with
    | zero =>
      change (0 : ℕ).testBit q = _
      simp
    | succ n ih =>
      change (1 ||| _ <<< 384 : ℕ).testBit q = _
      rw [Nat.testBit_or, testBit_one', Nat.testBit_shiftLeft, Bool.eq_iff_iff]
      by_cases hq : 384 ≤ q
      · rw [ih (q - 384)]
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
        omega
      · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
        omega
  exact key 128

theorem repN_field (h : ℕ) : repN / 2 ^ (384 * h) % 2 ^ 384 = if h < 128 then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 384
  · rw [testBit_field _ _ _ _ hr, testBit_repN]
    by_cases hh : h < 128
    · rw [if_pos hh, testBit_one', Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      omega
    · rw [if_neg hh, Nat.zero_testBit]
      exact decide_eq_false (by omega)
  · rw [Nat.testBit_mod_two_pow]
    have : (if h < 128 then 1 else 0 : ℕ) < 2 ^ 384 := by split <;> norm_num
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num)
      (by omega)))]
    simp [hr]

theorem repN_mul_field (y h : ℕ) (hy : y < 2 ^ 384) :
    repN * y / 2 ^ (384 * h) % 2 ^ 384 = if h < 128 then y else 0 := by
  have hb : ∀ γ, repN / 2 ^ (384 * γ) % 2 ^ 384 * y < 2 ^ 384 := fun γ => by
    rw [repN_field]
    split
    · rw [Nat.one_mul]
      exact hy
    · rw [Nat.zero_mul]
      exact Nat.two_pow_pos _
  rw [fieldMul 384 h repN y hb, repN_field]
  split
  · rw [Nat.one_mul]
  · rw [Nat.zero_mul]

theorem testBit_repN_mul (y q : ℕ) (hy : y < 2 ^ 384) :
    (repN * y).testBit q = (decide (q / 384 < 128) && y.testBit (q % 384)) := by
  have e : q = 384 * (q / 384) + q % 384 := (Nat.div_add_mod q 384).symm
  rw [e, ← testBit_field _ _ _ _ (Nat.mod_lt q (by norm_num)), repN_mul_field y _ hy]
  rw [← e]
  by_cases hq : q / 384 < 128
  · rw [if_pos hq, decide_eq_true hq, Bool.true_and]
  · rw [if_neg hq, decide_eq_false hq, Bool.false_and, Nat.zero_testBit]

theorem testBit_spread (v q : ℕ) :
    (spread v).testBit q = (decide (q % 32 = 0 ∧ q / 32 < 12) && v.testBit (q / 32)) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
      (fun r ih => Nat.lor ih (Nat.shiftLeft fld(v, r, 1) (Nat.mul 32 r))) n : ℕ).testBit q =
      (decide (q % 32 = 0 ∧ q / 32 < n) && v.testBit (q / 32)) := by
    intro n
    induction n with
    | zero =>
      change (0 : ℕ).testBit q = _
      simp
    | succ n ih =>
      change (_ ||| _ <<< (32 * n) : ℕ).testBit q = _
      rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft, fld1_eq, testBit_ite01]
      by_cases hq : q = 32 * n
      · subst hq
        simp
      · have h1 : (decide (32 * n ≤ q) && (v.testBit n && decide (q - 32 * n = 0))) = false := by
          have : q - 32 * n ≠ 0 ∨ ¬ 32 * n ≤ q := by omega
          rcases this with h | h <;> simp [h]
        rw [h1, Bool.or_false]
        by_cases h2 : q % 32 = 0 ∧ q / 32 < n
        · have h3 : q % 32 = 0 ∧ q / 32 < n + 1 := ⟨h2.1, by omega⟩
          rw [decide_eq_true h2, decide_eq_true h3]
        · have h3 : ¬ (q % 32 = 0 ∧ q / 32 < n + 1) := by omega
          rw [decide_eq_false h2, decide_eq_false h3]
  exact key 12

theorem spread_lt (v : ℕ) : spread v < 2 ^ 353 := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  rw [testBit_spread]
  have : ¬ (i % 32 = 0 ∧ i / 32 < 12) := by omega
  simp [this]

theorem spread_field (v r : ℕ) :
    spread v / 2 ^ (32 * r) % 2 ^ 32 = if r < 12 ∧ v.testBit r = true then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 32
  · rw [testBit_field _ _ _ _ hb, testBit_spread]
    have e1 : (32 * r + b) / 32 = r := by omega
    rw [e1]
    by_cases hc : r < 12 ∧ v.testBit r = true
    · rw [if_pos hc, testBit_one']
      by_cases hb0 : b = 0
      · subst hb0
        simp [hc.1, hc.2]
      · have hd : decide ((32 * r + b) % 32 = 0 ∧ r < 12) = false := decide_eq_false (by omega)
        rw [hd, Bool.false_and]
        simp [hb0]
    · rw [if_neg hc, Nat.zero_testBit]
      by_cases hr : r < 12
      · have : v.testBit r = false := by simpa [hr] using hc
        simp [this]
      · simp [hr]
  · rw [Nat.testBit_mod_two_pow]
    have : (if r < 12 ∧ v.testBit r = true then 1 else 0 : ℕ) < 2 ^ b := by
      split
      · exact Nat.one_lt_two_pow (by omega)
      · exact Nat.two_pow_pos b
    rw [Nat.testBit_eq_false_of_lt this]
    simp [hb]

theorem testBit_spread_mul {v x : ℕ} (hx : ∀ h, x / 2 ^ (384 * h) % 2 ^ 384 < 2 ^ 30)
    {h r j : ℕ} (hr : r < 12) (hj : j < 30) :
    (x * spread v).testBit (384 * h + (32 * r + j)) = (v.testBit r && x.testBit (384 * h + j)) := by
  have h1 : ∀ γ, x / 2 ^ (384 * γ) % 2 ^ 384 * spread v < 2 ^ 384 := fun γ =>
    calc _ < 2 ^ 30 * 2 ^ 353 := Nat.mul_lt_mul'' (hx γ) (spread_lt v)
      _ ≤ 2 ^ 384 := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  rw [← testBit_field _ _ _ _ (by omega : 32 * r + j < 384), fieldMul 384 h x _ h1]
  set xh := x / 2 ^ (384 * h) % 2 ^ 384 with hxh
  have h2 : ∀ γ, spread v / 2 ^ (32 * γ) % 2 ^ 32 * xh < 2 ^ 32 := fun γ => by
    rw [spread_field]
    split
    · rw [Nat.one_mul]
      exact lt_of_lt_of_le (hx h) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    · rw [Nat.zero_mul]
      exact Nat.two_pow_pos 32
  rw [Nat.mul_comm, ← testBit_field _ _ 32 _ (by omega), fieldMul 32 r _ xh h2, spread_field]
  have hjx : xh.testBit j = x.testBit (384 * h + j) := testBit_field x _ 384 j (by omega)
  by_cases hv : v.testBit r = true
  · simp [hr, hv, hjx]
  · have : v.testBit r = false := by simpa using hv
    simp [this]

theorem bitZ'_mulRowK_aux (R LN q : ℕ) : ∀ (sp : List ℕ) (c : ℕ),
    bitZ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun s _ ih c => Nat.xor (Nat.mul s (Nat.land (Nat.shiftRight R (Nat.mul 32 c)) LN)) (ih (Nat.succ c)))
      sp c : ℕ) q =
      ∑ i ∈ Finset.range sp.length, bitZ (sp.getD i 0 * ((R >>> (32 * (c + i))) &&& LN)) q
  | [], c => by
    change bitZ 0 q = _
    simp [bitZ]
  | s :: sp, c => by
    have ih := bitZ'_mulRowK_aux R LN q sp (c + 1)
    have e : ∀ i, c + 1 + i = c + (i + 1) := fun i => by omega
    simp only [e] at ih
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [← ih]
    change bitZ ((s * ((R >>> (32 * c)) &&& LN)) ^^^ _) q = _
    rw [bitZ_xor, add_comm]

theorem testBit_LN (q : ℕ) :
    (repN * 1073741823).testBit q = (decide (q / 384 < 128) && decide (q % 384 < 30)) := by
  have hl : (1073741823 : ℕ) < 2 ^ 384 :=
    Nat.lt_of_lt_of_le (by norm_num : (1073741823 : ℕ) < 2 ^ 30)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  rw [testBit_repN_mul _ _ hl, show (1073741823 : ℕ) = 2 ^ 30 - 1 by norm_num,
    Nat.testBit_two_pow_sub_one]

theorem LN_field (R h : ℕ) : (R &&& repN * 1073741823) / 2 ^ (384 * h) % 2 ^ 384 < 2 ^ 30 := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  by_cases hi' : i < 384
  · rw [testBit_field _ _ _ _ hi', Nat.testBit_and, testBit_LN]
    have : ¬ (384 * h + i) % 384 < 30 := by omega
    rw [decide_eq_false this]
    simp
  · rw [Nat.testBit_mod_two_pow]
    simp [hi']

theorem bitZ'_mulRowK {sp : List ℕ} {V : List ℕ} (hsp : sp = V.map spread) (R : ℕ) {h r j : ℕ}
    (hh : h < 128) (hr : r < 12) (hj : j < 30) :
    bitZ (mulRowK sp R (repN * 1073741823)) (384 * h + (32 * r + j)) =
      ∑ i ∈ Finset.range V.length, bitZ (V.getD i 0) r * bitZ R (384 * h + (32 * i + j)) := by
  have e := bitZ'_mulRowK_aux R (repN * 1073741823) (384 * h + (32 * r + j)) sp 0
  change bitZ (mulRowK sp R (repN * 1073741823)) _ = _ at e
  rw [e, hsp, List.length_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < V.length := Finset.mem_range.1 hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, Nat.mul_comm]
  unfold bitZ
  rw [testBit_spread_mul (fun h' => LN_field (R >>> (32 * (0 + i))) h') hr hj, Nat.testBit_and,
    Nat.testBit_shiftRight, testBit_LN, List.getD_eq_getElem _ _ hi']
  have e1 : (384 * h + j) / 384 = h := by omega
  have e2 : (384 * h + j) % 384 = j := by omega
  rw [e1, e2, show 32 * (0 + i) + (384 * h + j) = 384 * h + (32 * i + j) by omega]
  simp only [decide_eq_true hh, decide_eq_true hj, Bool.true_and, Bool.and_true]
  cases V[i].testBit r <;> cases R.testBit (384 * h + (32 * i + j)) <;> simp

theorem norm_num' {HP : ℕ} (h : normK HP = true) :
    ∀ j < 30, ∀ x < 128, hv HP j 0 x = 0 ∧ hv HP j x 0 = 0 := by
  intro j hj x hx
  change bAnd(Nat.beq (rowAt HP 0) 0, allN 128 (fun x => Nat.beq (fieldAt (rowAt HP x) 0) 0)) = true
    at h
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, CFSG.KS.PK.allN_iff] at h
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, hvR_zero_of_fieldAt (beq_true (h1 x hx)) hj⟩
  change hvR (rowAt HP 0) j x = 0
  rw [beq_true h0]
  exact hvR_zero_left j x

theorem tree_num {HP LMP GP PP : ℕ} (h : treeK HP GP PP = true)
    (hd : dataK GP PP LMP genT parT lT = true) :
    ∀ j < 30, ∀ x, x ≠ 0 → x < 128 → hv HP j (gen x + 1) (par x) = 0 := by
  intro j hj x hx0 hx
  obtain ⟨hg, hp, -⟩ := data_spec hd
  have e := beq_true (CFSG.KS.PK.allN_iff.1 h (x - 1) (by omega))
  have hx1 : Nat.succ (x - 1) = x := by omega
  rw [hx1, hg x hx, hp x hx] at e
  exact hvR_zero_of_fieldAt e hj

theorem free_num {HP : ℕ} (h : freeK HP h2Free = true) :
    ∀ i < 30, h2Free.getD i 0 < 4608 ∧ ∀ j < 30,
      (hv HP j (h2Free.getD i 0 / 1536 + 1) (h2Free.getD i 0 / 12 % 128)).testBit
        (h2Free.getD i 0 % 12) = decide (i = j) := by
  have hl : h2Free.length = 30 := by decide
  intro i hi
  have h' : freeL HP h2Free 0 = true := h
  obtain ⟨h1, h2⟩ := freeL_spec h' i (hl ▸ hi)
  refine ⟨h1, fun j hj => ?_⟩
  have e := h2 j hj
  have hb : bitF HP j (h2Free.getD i 0) = if (rowAt HP (h2Free.getD i 0 / 1536 + 1)).testBit
      (384 * (h2Free.getD i 0 / 12 % 128) + (32 * (h2Free.getD i 0 % 12) + j)) then 1 else 0 :=
    fld1_eq _ _
  rw [hb, Nat.zero_add] at e
  change (hvR _ j _).testBit _ = _
  rw [testBit_hvR, decide_eq_true (Nat.mod_lt _ (by decide)), Bool.true_and]
  revert e
  cases (rowAt HP (h2Free.getD i 0 / 1536 + 1)).testBit
      (384 * (h2Free.getD i 0 / 12 % 128) + (32 * (h2Free.getD i 0 % 12) + j)) <;>
    by_cases hij : i = j <;> simp [hij]

theorem mulIdx_zero' (h : ℕ) : mulIdx 0 h = h := by
  rw [mulIdx, path_zero, List.foldr_nil]

theorem mulIdx_cons' {x : ℕ} (hx0 : x ≠ 0) (hx : x < 128) (h : ℕ) :
    mulIdx x h = lmul (gen x) (mulIdx (par x) h) := by
  rw [mulIdx, path_cons hx0 hx, List.foldr_cons, ← mulIdx]

theorem mt_spec {MTP LMP GP PP : ℕ} (hmt : mtK MTP LMP GP PP = true)
    (hd : dataK GP PP LMP genT parT lT = true) :
    ∀ x < 128, ∀ h < 128, pg 7 127 MTP (128 * x + h) = mulIdx x h := by
  obtain ⟨hg, hp, hl⟩ := data_spec hd
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx h hh
    have e := beq_true (CFSG.KS.PK.allN_iff.1 (CFSG.KS.PK.allN_iff.1 hmt x hx) h hh)
    rw [CFSG.KS.PK.nIf_eq] at e
    change pg 7 127 MTP (128 * x + h) = _ at e
    by_cases hx0 : x = 0
    · subst hx0
      rw [e, mulIdx_zero']
      simp
    · have hb : Nat.beq x 0 = false := by
        cases hb : Nat.beq x 0
        · rfl
        · exact absurd (beq_true hb) hx0
      rw [e, hb]
      simp only [Bool.false_eq_true, if_false]
      have hpx := par_lt hx0
      change pg 7 127 LMP (128 * pg 2 3 GP x + pg 7 127 MTP (128 * pg 7 127 PP x + h)) = _
      rw [hg x hx, hp x hx, ih _ hpx (hpx.trans hx) h hh, mulIdx_cons' hx0 hx,
        hl _ (gen_lt x) _ (mulIdx_spec hh).1]

@[expose] noncomputable def Hc (HP j : ℕ) (s t : ↥S) : V12 := bv (hv HP j (idx s) (idx t))

theorem idx_one' : idx (1 : ↥S) = 0 := by
  rw [← elt_zero, idx_elt (by norm_num)]

theorem Hc_elt (HP j : ℕ) {x t : ℕ} (hx : x < 128) (ht : t < 128) :
    Hc HP j (elt x) (elt t) = bv (hv HP j x t) := by
  rw [Hc, idx_elt hx, idx_elt ht]

theorem treeZero_Hc {HP LMP GP PP : ℕ} (h : treeK HP GP PP = true)
    (hd : dataK GP PP LMP genT parT lT = true) {j : ℕ} (hj : j < 30) : TreeZero (Hc HP j) := by
  intro x hx0 hx
  have hp : par x < 128 := (par_lt hx0).trans hx
  rw [← elt_succ (gen_lt x), Hc_elt HP j (by have := gen_lt x; omega) hp,
    tree_num h hd j hj x hx0 hx, bv_zero]

theorem coordF_Hc {HP : ℕ} (h : freeK HP h2Free = true) {i j : ℕ} (hi : i < 30) (hj : j < 30) :
    coordF (Hc HP j) (h2Free.getD i 0) = if i = j then 1 else 0 := by
  obtain ⟨hf, hb⟩ := free_num h i hi
  have hk : h2Free.getD i 0 / 1536 < 3 := by omega
  rw [coordF, ← elt_succ hk, Hc_elt HP j (by omega) (Nat.mod_lt _ (by norm_num))]
  simp only [bv, hb j hj, decide_eq_true_eq]

end CFSG.KC.J2H2

end
