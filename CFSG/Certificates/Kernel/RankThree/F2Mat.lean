module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.Native.F2

open CFSG.Monster.B.Co2.Native

variable (d : ℕ)

@[expose] def row (M k : ℕ) : ℕ := (M >>> (d * k)) % 2 ^ d

@[expose] def vmul (v M : ℕ) : ℕ :=
  (List.range d).foldr (fun k acc => if v.testBit k then row d M k ^^^ acc else acc) 0

@[expose] def mmul (A B : ℕ) : ℕ :=
  (List.range d).foldr (fun k acc => (vmul d (row d A k) B <<< (d * k)) ||| acc) 0

@[expose] def vidx (V : Array ℕ) (x : ℕ) : ℕ := V.toList.idxOf x

@[expose] def permOfMat (V : Array ℕ) (M : ℕ) : Array ℕ := V.map fun v => vidx V (vmul d v M)

variable {d}

@[expose] def bz (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bz_xor (a b : Bool) : bz (a ^^ b) = bz a + bz b := by
  cases a <;> cases b <;> decide

theorem bz_and (a b : Bool) : bz (a && b) = bz a * bz b := by
  cases a <;> cases b <;> decide

theorem bz_inj {a b : Bool} (h : bz a = bz b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem bz_fold (L : List ℕ) (p : ℕ → Bool) :
    bz (L.foldr (fun k b => p k ^^ b) false) = (L.map fun k => bz (p k)).sum := by
  induction L with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, bz_xor, ih, List.map_cons, List.sum_cons]

theorem testBit_row (M k j : ℕ) :
    (row d M k).testBit j = (decide (j < d) && M.testBit (d * k + j)) := by
  rw [row, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem row_lt (M k : ℕ) : row d M k < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)

theorem testBit_vmul (v M j : ℕ) :
    (vmul d v M).testBit j =
      (List.range d).foldr (fun k b => (v.testBit k && (row d M k).testBit j) ^^ b) false := by
  unfold vmul
  induction List.range d with
  | nil => simp
  | cons k l ih =>
    simp only [List.foldr_cons]
    by_cases hv : v.testBit k
    · simp [hv, Nat.testBit_xor, ih]
    · simp [hv, ih]

theorem vmul_lt (v M : ℕ) : vmul d v M < 2 ^ d := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_vmul]
  induction List.range d with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldr_cons, ih, Bool.xor_false, Nat.testBit_lt_two_pow (lt_of_lt_of_le (row_lt M k)
      (Nat.pow_le_pow_right (by norm_num) hj)), Bool.and_false]

theorem testBit_blocks (f : ℕ → ℕ) (hf : ∀ k, f k < 2 ^ d) (L : List ℕ) {k j : ℕ} (hj : j < d) :
    (L.foldr (fun k acc => (f k <<< (d * k)) ||| acc) 0).testBit (d * k + j) =
      (decide (k ∈ L) && (f k).testBit j) := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases hak : a = k
    · subst hak
      simp only [ge_iff_le, Nat.le_add_right, decide_true, Nat.add_sub_cancel_left, Bool.true_and,
        List.mem_cons, true_or]
      cases (f a).testBit j <;> simp
    · have hmem : decide (k ∈ a :: l) = decide (k ∈ l) := by
        simp [List.mem_cons, Ne.symm hak]
      rw [hmem]
      have hz : (decide (d * a ≤ d * k + j) && (f a).testBit (d * k + j - d * a)) = false := by
        rcases Nat.lt_or_gt_of_ne hak with h | h
        · have h1 : d * a + d ≤ d * k := by
            have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h)
            rw [Nat.mul_succ] at this
            exact this
          have h2 : d ≤ d * k + j - d * a := by omega
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf a) (Nat.pow_le_pow_right (by norm_num) h2)),
            Bool.and_false]
        · have h1 : d * k + d ≤ d * a := by
            have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h)
            rw [Nat.mul_succ] at this
            exact this
          have : ¬ d * a ≤ d * k + j := by omega
          simp [this]
      rw [hz, Bool.false_or]

theorem row_mmul (A B : ℕ) {k : ℕ} (hk : k < d) : row d (mmul d A B) k = vmul d (row d A k) B := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_row]
  by_cases hj : j < d
  · rw [decide_eq_true hj, Bool.true_and, mmul,
      testBit_blocks (fun k => vmul d (row d A k) B) (fun k => vmul_lt _ _) _ hj]
    simp [List.mem_range, hk]
  · rw [decide_eq_false hj, Bool.false_and,
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (vmul_lt _ _)
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hj)))]

theorem sum_range_list (n : ℕ) (f : ℕ → ZMod 2) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem bz_testBit_vmul (v M j : ℕ) :
    bz ((vmul d v M).testBit j) =
      ∑ k ∈ Finset.range d, bz (v.testBit k) * bz ((row d M k).testBit j) := by
  rw [testBit_vmul, bz_fold, sum_range_list]
  simp only [bz_and]

theorem vmul_mmul (v A B : ℕ) : vmul d v (mmul d A B) = vmul d (vmul d v A) B := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply bz_inj
  rw [bz_testBit_vmul, bz_testBit_vmul]
  have hrow : ∀ k ∈ Finset.range d, bz ((row d (mmul d A B) k).testBit j) =
      ∑ m ∈ Finset.range d, bz ((row d A k).testBit m) * bz ((row d B m).testBit j) := by
    intro k hk
    rw [row_mmul A B (Finset.mem_range.1 hk), bz_testBit_vmul]
  rw [Finset.sum_congr rfl fun k hk => by rw [hrow k hk]]
  simp only [bz_testBit_vmul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem vmul_xor (x y M : ℕ) : vmul d (x ^^^ y) M = vmul d x M ^^^ vmul d y M := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply bz_inj
  rw [Nat.testBit_xor, bz_xor, bz_testBit_vmul, bz_testBit_vmul, bz_testBit_vmul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.testBit_xor, bz_xor]
  ring

theorem vmul_zero (M : ℕ) : vmul d 0 M = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply bz_inj
  rw [bz_testBit_vmul]
  simp [bz]

theorem vmul_unit (M : ℕ) {k : ℕ} (hk : k < d) : vmul d (2 ^ k) M = row d M k := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply bz_inj
  rw [bz_testBit_vmul, Finset.sum_eq_single k]
  · simp [bz, Nat.testBit_two_pow_self]
  · intro b _ hb
    simp [bz, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_range.2 hk) h

theorem mat_ext {A B : ℕ} (hA : A < 2 ^ (d * d)) (hB : B < 2 ^ (d * d))
    (h : ∀ k < d, row d A k = row d B k) : A = B := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < d * d
  · have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        simp at ht
      · exact h0
    have hk : t / d < d := (Nat.div_lt_iff_lt_mul hd).2 ht
    have e : t = d * (t / d) + t % d := (Nat.div_add_mod t d).symm
    have h1 := congrArg (fun x => x.testBit (t % d)) (h (t / d) hk)
    simp only [testBit_row, decide_eq_true (Nat.mod_lt t hd), Bool.true_and] at h1
    rw [e]
    exact h1
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_of_not_lt ht))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hB
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt ht)))]

theorem getElem_vidx {V : Array ℕ} {x : ℕ} (h : x ∈ V) : vidx V x < V.size ∧ V[vidx V x]! = x := by
  have hl : V.toList.idxOf x < V.toList.length :=
    List.idxOf_lt_length_of_mem (Array.mem_toList_iff.2 h)
  rw [Array.length_toList] at hl
  refine ⟨hl, ?_⟩
  rw [getElem!_pos V _ hl]
  simp only [vidx, ← Array.getElem_toList]
  exact List.getElem_idxOf (by simpa using hl)

theorem permOfMat_size (V : Array ℕ) (M : ℕ) : (permOfMat d V M).size = V.size := by
  simp [permOfMat]

theorem permOfMat_get {V : Array ℕ} {M i : ℕ} (hi : i < V.size) :
    (permOfMat d V M)[i]! = vidx V (vmul d V[i]! M) := by
  rw [getElem!_pos _ i (by rw [permOfMat_size]; exact hi), getElem!_pos V i hi]
  simp [permOfMat]

theorem permOfMat_mmul {V : Array ℕ} {A B : ℕ} (hA : ∀ v ∈ V, vmul d v A ∈ V) :
    permOfMat d V (mmul d A B) = compA V.size (permOfMat d V B) (permOfMat d V A) := by
  apply Array.ext
  · simp [permOfMat, compA]
  · intro i h1 h2
    have hi : i < V.size := by simpa [permOfMat] using h1
    have e1 : (permOfMat d V (mmul d A B))[i] = (permOfMat d V (mmul d A B))[i]! :=
      (getElem!_pos _ i h1).symm
    rw [e1, permOfMat_get hi]
    simp only [compA, Array.getElem_ofFn]
    rw [permOfMat_get hi]
    have hmem : vmul d V[i]! A ∈ V := hA _ (by rw [getElem!_pos V i hi]; exact Array.getElem_mem hi)
    obtain ⟨hlt, hget⟩ := getElem_vidx hmem
    rw [permOfMat_get hlt, hget, vmul_mmul]

variable (d) in
@[expose] def bs (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 ^ (d * m) * f m + bs f m

variable (d) in
@[expose] def lanes : ℕ := bs d (fun _ => 1) d

variable (d) in
@[expose] def mulL (A B : ℕ) : ℕ :=
  (List.range d).foldr (fun j acc =>
    ((((A >>> j) &&& lanes d) * (2 ^ d - 1)) &&& (row d B j * lanes d)) ^^^ acc) 0

theorem bs_lt {f : ℕ → ℕ} (hf : ∀ k, f k < 2 ^ d) (m : ℕ) : bs d f m < 2 ^ (d * m) := by
  induction m with
  | zero => simp [bs]
  | succ m ih =>
    rw [bs, Nat.mul_succ, Nat.pow_add]
    have := hf m
    have h2 : 0 < 2 ^ (d * m) := Nat.two_pow_pos _
    nlinarith

theorem testBit_bs (hd : 0 < d) {f : ℕ → ℕ} (hf : ∀ k, f k < 2 ^ d) (m t : ℕ) :
    (bs d f m).testBit t = (decide (t / d < m) && (f (t / d)).testBit (t % d)) := by
  induction m with
  | zero => simp [bs]
  | succ m ih =>
    rw [bs, Nat.testBit_two_pow_mul_add _ (bs_lt hf m)]
    by_cases ht : t < d * m
    · simp only [ht, ↓reduceIte]
      rw [ih]
      have : t / d < m := (Nat.div_lt_iff_lt_mul hd).2 (by rw [Nat.mul_comm]; exact ht)
      simp [this, Nat.lt_succ_of_lt this]
    · simp only [ht, ↓reduceIte]
      by_cases ht2 : t < d * m + d
      · have hq : t / d = m := by
          apply Nat.div_eq_of_lt_le
          · rw [Nat.mul_comm]; omega
          · rw [Nat.succ_mul, Nat.mul_comm]; omega
        have hr : t - d * m = t % d := by
          have := Nat.div_add_mod t d
          rw [hq] at this
          omega
        rw [hq, hr]
        simp
      · have hq : m + 1 ≤ t / d := by
          rw [Nat.le_div_iff_mul_le hd]
          rw [Nat.succ_mul, Nat.mul_comm]
          omega
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf m) (Nat.pow_le_pow_right (by norm_num)
          (by omega)))]
        have hn : ¬ t / d < m + 1 := by omega
        simp [hn]

theorem bs_congr {f g : ℕ → ℕ} {m : ℕ} (h : ∀ k < m, f k = g k) : bs d f m = bs d g m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [bs, bs, h m (Nat.lt_succ_self m), ih fun k hk => h k (Nat.lt_succ_of_lt hk)]

theorem bs_zero (m : ℕ) : bs d (fun _ => 0) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [bs, ih]; simp

theorem bs_mul (f : ℕ → ℕ) (c m : ℕ) : bs d f m * c = bs d (fun k => f k * c) m := by
  induction m with
  | zero => simp [bs]
  | succ m ih => rw [bs, bs, ← ih]; ring

theorem bs_ext (hd : 0 < d) {g : ℕ → ℕ} (hg : ∀ k, g k < 2 ^ d)
    {x : ℕ} (m : ℕ) (h : ∀ t, x.testBit t = (decide (t / d < m) && (g (t / d)).testBit (t % d))) :
    x = bs d g m := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [h, testBit_bs hd hg]

theorem bs_and (hd : 0 < d) {f g : ℕ → ℕ} (hf : ∀ k, f k < 2 ^ d) (hg : ∀ k, g k < 2 ^ d)
    (m : ℕ) : bs d f m &&& bs d g m = bs d (fun k => f k &&& g k) m := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and, testBit_bs hd hf, testBit_bs hd hg,
    testBit_bs hd (fun k => Nat.and_lt_two_pow _ (hg k)), Nat.testBit_and]
  cases decide (t / d < m) <;> simp

theorem bs_xor (hd : 0 < d) {f g : ℕ → ℕ} (hf : ∀ k, f k < 2 ^ d) (hg : ∀ k, g k < 2 ^ d)
    (m : ℕ) : bs d f m ^^^ bs d g m = bs d (fun k => f k ^^^ g k) m := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_xor, testBit_bs hd hf, testBit_bs hd hg,
    testBit_bs hd (fun k => Nat.xor_lt_two_pow (hf k) (hg k)), Nat.testBit_xor]
  cases decide (t / d < m) <;> simp

theorem row_bs (hd : 0 < d) {f : ℕ → ℕ} (hf : ∀ k, f k < 2 ^ d) {m k : ℕ} (hk : k < m) :
    row d (bs d f m) k = f k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_row, testBit_bs hd hf]
  by_cases hj : j < d
  · have h1 : (d * k + j) / d = k := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
    have h2 : (d * k + j) % d = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    simp [hj, h1, h2, hk]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf k) (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_of_not_lt hj)))]
    simp [hj]

theorem shift_lanes (hd : 0 < d) (A j : ℕ) :
    (A >>> j) &&& lanes d = bs d (fun k => if A.testBit (d * k + j) then 1 else 0) d := by
  have h1 : ∀ k : ℕ, (fun _ : ℕ => 1) k < 2 ^ d := fun _ => Nat.one_lt_two_pow (by omega)
  have h2 : ∀ k : ℕ, (fun k => if A.testBit (d * k + j) then 1 else 0) k < 2 ^ d := by
    intro k
    dsimp only
    split
    · exact Nat.one_lt_two_pow (by omega)
    · exact Nat.two_pow_pos d
  have key : ∀ i : ℕ, (1 : ℕ).testBit i = decide (i = 0) := by
    intro i
    rw [Bool.eq_iff_iff, Nat.testBit_one_eq_true_iff_self_eq_zero, decide_eq_true_iff]
  have key2 : ∀ (b : Bool) (i : ℕ), (if b then (1 : ℕ) else 0).testBit i = (b && decide (i = 0)) := by
    intro b i
    cases b <;> simp [key]
  apply bs_ext hd h2
  intro t
  rw [Nat.testBit_and, Nat.testBit_shiftRight, lanes, testBit_bs hd h1, key, key2]
  by_cases h0 : t % d = 0
  · have et : j + t = d * (t / d) + j := by
      have := Nat.div_add_mod t d
      omega
    rw [et]
    cases A.testBit (d * (t / d) + j) <;> cases decide (t / d < d) <;> simp [h0]
  · simp [h0]

theorem mmul_lt (A B : ℕ) : mmul d A B < 2 ^ (d * d) := by
  unfold mmul
  have : ∀ L : List ℕ, (∀ k ∈ L, k < d) →
      L.foldr (fun k acc => (vmul d (row d A k) B <<< (d * k)) ||| acc) 0 < 2 ^ (d * d) := by
    intro L hL
    induction L with
    | nil => exact Nat.two_pow_pos _
    | cons k l ih =>
      rw [List.foldr_cons]
      refine Nat.or_lt_two_pow ?_ (ih fun j hj => hL j (List.mem_cons_of_mem _ hj))
      have hk := hL k List.mem_cons_self
      rw [Nat.shiftLeft_eq]
      calc vmul d (row d A k) B * 2 ^ (d * k) < 2 ^ d * 2 ^ (d * k) :=
            Nat.mul_lt_mul_of_pos_right (vmul_lt _ _) (Nat.two_pow_pos _)
        _ = 2 ^ (d * (k + 1)) := by rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
        _ ≤ 2 ^ (d * d) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hk)
  exact this _ fun k hk => List.mem_range.1 hk

theorem mmul_eq_bs (hd : 0 < d) (A B : ℕ) :
    mmul d A B = bs d (fun k => vmul d (row d A k) B) d :=
  mat_ext (mmul_lt A B) (bs_lt (fun k => vmul_lt _ _) d) fun k hk => by
    rw [row_mmul A B hk, row_bs hd (fun k => vmul_lt _ _) hk]

theorem fold_xor_lt {g : ℕ → ℕ} (L : List ℕ) (hg : ∀ j ∈ L, g j < 2 ^ d) :
    L.foldr (fun j acc => g j ^^^ acc) 0 < 2 ^ d := by
  induction L with
  | nil => exact Nat.two_pow_pos _
  | cons j l ih =>
    exact Nat.xor_lt_two_pow (hg j List.mem_cons_self)
      (ih fun i hi => hg i (List.mem_cons_of_mem _ hi))

theorem mulL_eq (hd : 0 < d) (A B : ℕ) : mulL d A B = mmul d A B := by
  have hlt : ∀ (c : Bool) (j : ℕ), (if c then row d B j else 0) < 2 ^ d := by
    intro c j
    cases c
    · exact Nat.two_pow_pos d
    · exact row_lt B j
  have hterm : ∀ j < d, ((((A >>> j) &&& lanes d) * (2 ^ d - 1)) &&& (row d B j * lanes d)) =
      bs d (fun k => if A.testBit (d * k + j) then row d B j else 0) d := by
    intro j hj
    have h1 : ∀ k, (fun k => (if A.testBit (d * k + j) then 1 else 0) * (2 ^ d - 1)) k < 2 ^ d := by
      intro k
      dsimp only
      split
      · rw [Nat.one_mul]
        exact Nat.sub_lt (Nat.two_pow_pos d) Nat.one_pos
      · rw [Nat.zero_mul]
        exact Nat.two_pow_pos d
    have h2 : ∀ k : ℕ, (fun _ : ℕ => 1 * row d B j) k < 2 ^ d := fun k => by
      rw [Nat.one_mul]
      exact row_lt B j
    rw [shift_lanes hd A j, bs_mul, lanes, Nat.mul_comm (row d B j), bs_mul, bs_and hd h1 h2]
    apply bs_congr
    intro k _
    split
    · rw [Nat.one_mul, Nat.one_mul, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (row_lt B j)]
    · rw [Nat.zero_mul, Nat.zero_and]
  have hfold : ∀ L : List ℕ, (∀ j ∈ L, j < d) →
      L.foldr (fun j acc =>
        ((((A >>> j) &&& lanes d) * (2 ^ d - 1)) &&& (row d B j * lanes d)) ^^^ acc) 0 =
      bs d (fun k => L.foldr (fun j acc =>
        (if A.testBit (d * k + j) then row d B j else 0) ^^^ acc) 0) d := by
    intro L hL
    induction L with
    | nil => exact (bs_zero d).symm
    | cons j l ih =>
      rw [List.foldr_cons, hterm j (hL j List.mem_cons_self),
        ih fun i hi => hL i (List.mem_cons_of_mem _ hi),
        bs_xor hd (fun k => hlt _ _) (fun k => fold_xor_lt l fun i _ => hlt _ _)]
      rfl
  rw [mulL, hfold _ fun j hj => List.mem_range.1 hj, mmul_eq_bs hd]
  apply bs_congr
  intro k _
  unfold vmul
  have : ∀ L : List ℕ, (∀ j ∈ L, j < d) →
      L.foldr (fun j acc => (if A.testBit (d * k + j) then row d B j else 0) ^^^ acc) 0 =
      L.foldr (fun j acc => if (row d A k).testBit j then row d B j ^^^ acc else acc) 0 := by
    intro L hL
    induction L with
    | nil => rfl
    | cons j l ih =>
      rw [List.foldr_cons, List.foldr_cons, ih fun i hi => hL i (List.mem_cons_of_mem _ hi),
        testBit_row, decide_eq_true (hL j List.mem_cons_self), Bool.true_and]
      split
      · rfl
      · rw [Nat.zero_xor]
  exact this _ fun j hj => List.mem_range.1 hj

end CFSG.RankThree.Native.F2

end
