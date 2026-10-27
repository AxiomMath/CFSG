module

public import Certificates.Data.Kernel.KDense.Init
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KC.KDense

open CFSG.Monster.AxisCount

@[expose] noncomputable def res15 (v : Native.DVec) (k : ℕ) : ZMod 15 := (v.D.getD k 0 : ZMod 15) * 8 ^ v.e

@[expose] noncomputable def resP (S x p : ℕ) : ZMod 15 :=
  ((x / 2 ^ p % 2 + 2 * (x / 2 ^ (S + p) % 2) + 4 * (x / 2 ^ (2 * S + p) % 2) +
    8 * (x / 2 ^ (3 * S + p) % 2) : ℕ) : ZMod 15)

@[expose] noncomputable def xposK (q : ℕ) : ℕ :=
  if q < 552 then (if q % 2 = 0 then 114688 else 115712) + 32 * (Native.pairTab ())[q / 2]!.1 +
    (Native.pairTab ())[q / 2]!.2
  else if q < 49704 then 32 * ((q - 552) / 24) + (q - 552) % 24 else 65536 + (q - 49704)

@[expose] def Rep (v : Native.DVec) (s : St) : Prop :=
  (∀ q < 98280, resP SX s.2.1 (xposK q) = res15 v (300 + q)) ∧
  (∀ p < SX, (∀ q < 98280, xposK q ≠ p) → resP SX s.2.1 p = 0) ∧ s.2.1 < 2 ^ (4 * SX) ∧
  (∀ i < 24, ∀ j < 24, resP SA s.2.2.1 (32 * i + j) = res15 v (Native.aIdx i j)) ∧
  (∀ p < SA, (24 ≤ p % 32 ∨ 24 ≤ p / 32) → resP SA s.2.2.1 p = 0) ∧ s.2.2.1 < 2 ^ (4 * SA) ∧
  (∀ r < 4096, ∀ j < 24, resP SX s.2.2.2 (32 * r + j) = res15 v (98580 + 24 * r + j)) ∧
  (∀ p < SX, 24 ≤ p % 32 → resP SX s.2.2.2 p = 0) ∧ s.2.2.2 < 2 ^ (4 * SX)

@[expose] noncomputable def dataOK (F : Fix) (T : Tab) (KT TH OCT DU1 : Nat) : Bool :=
  andB (thOK TH) (andB (octOK OCT) (andB (du1OK DU1) (andB (keysOK TH OCT DU1 KT)
    (andB (keyPlanesOK F KT) (andB (fixOK F) (tabOK F T))))))

@[expose] def ofATab (tab : Array Int) : Native.DVec :=
  ⟨0, Array.ofFn (n := 196884) fun k => if k.val < 300 then tab[k.val]! else 0⟩

@[expose] def ofRange (lo hi : ℕ) : Native.DVec :=
  ⟨0, Array.ofFn (n := 196884) fun k => if lo ≤ k.val ∧ k.val < hi then 1 else 0⟩

namespace InitAux

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

theorem lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl

theorem testBit_foldOr (g : ℕ → ℕ) (acc m y : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) acc (fun j a => Nat.lor a (g j)) m).testBit y = true ↔
      acc.testBit y = true ∨ ∃ j < m, (g j).testBit y = true := by
  induction m with
  | zero => simp
  | succ m ih =>
    change (Nat.lor (Nat.rec (motive := fun _ => ℕ) acc (fun j a => Nat.lor a (g j)) m)
      (g m)).testBit y = true ↔ _
    rw [lor_eq, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro ((h | ⟨j, hj, h⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, h⟩
      · exact Or.inr ⟨m, by omega, h⟩
    · rintro (h | ⟨j, hj, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inl (Or.inr ⟨j, hj, h⟩)
        · exact Or.inr h

theorem testBit_foldOr2 (G : ℕ → ℕ → ℕ) (acc m1 m2 y : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) acc
      (fun i a => Nat.rec (motive := fun _ => ℕ) a (fun j a2 => Nat.lor a2 (G i j)) m2) m1).testBit
        y = true ↔ acc.testBit y = true ∨ ∃ i < m1, ∃ j < m2, (G i j).testBit y = true := by
  induction m1 with
  | zero => simp
  | succ m ih =>
    change (Nat.rec (motive := fun _ => ℕ) (Nat.rec (motive := fun _ => ℕ) acc
      (fun i a => Nat.rec (motive := fun _ => ℕ) a (fun j a2 => Nat.lor a2 (G i j)) m2) m)
        (fun j a2 => Nat.lor a2 (G m j)) m2).testBit y = true ↔ _
    rw [testBit_foldOr, ih]
    constructor
    · rintro ((h | ⟨i, hi, j, hj, h⟩) | ⟨j, hj, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, j, hj, h⟩
      · exact Or.inr ⟨m, by omega, j, hj, h⟩
    · rintro (h | ⟨i, hi, j, hj, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inl (Or.inr ⟨i, hi, j, hj, h⟩)
        · exact Or.inr ⟨j, hj, h⟩

theorem bitN_toNat (r b : ℕ) : bitN r b = (r.testBit b).toNat := by
  change (r >>> b) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]

theorem testBit_bitN_shift (r b k y : ℕ) :
    (Nat.shiftLeft (bitN r b) k).testBit y = true ↔ y = k ∧ r.testBit b = true := by
  rw [bitN_toNat]
  cases r.testBit b
  · simp
  · change (1 <<< k).testBit y = true ↔ _
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp [eq_comm]

@[expose] noncomputable def put (S n r p : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun b acc => Nat.lor acc (Nat.shiftLeft (bitN r b) (Nat.add p (Nat.mul b S)))) n

theorem testBit_put (S n r p y : ℕ) :
    (put S n r p).testBit y = true ↔ ∃ b < n, y = p + b * S ∧ r.testBit b = true := by
  unfold put
  rw [testBit_foldOr (fun b => Nat.shiftLeft (bitN r b) (Nat.add p (Nat.mul b S)))]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, testBit_bitN_shift]
  rfl

theorem sum_bits (r n : ℕ) : ∑ b ∈ Finset.range n, 2 ^ b * (r / 2 ^ b % 2) = r % 2 ^ n := by
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]

theorem digit_eq {S n x p r : ℕ} (hr : r < 2 ^ n)
    (h : ∀ b < n, x.testBit (b * S + p) = r.testBit b) :
    ∑ b ∈ Finset.range n, 2 ^ b * (x / 2 ^ (b * S + p) % 2) = r := by
  rw [← Nat.mod_eq_of_lt hr, ← sum_bits]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [← Nat.toNat_testBit, ← Nat.toNat_testBit, h b (Finset.mem_range.1 hb)]

theorem resP_of_bits {S x p r : ℕ} (hr : r < 16)
    (h : ∀ b < 4, x.testBit (b * S + p) = r.testBit b) : resP S x p = (r : ZMod 15) := by
  have e := digit_eq (n := 4) (lt_of_lt_of_le hr (by decide)) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_mul, zero_add, one_mul, pow_zero,
    pow_one, Nat.reducePow] at e
  unfold resP
  congr 1

theorem resP_zero (S p : ℕ) : resP S 0 p = 0 := by simp [resP]

theorem res15I_lt (z : ℤ) : res15I z < 15 := by
  cases z with
  | ofNat n => exact Nat.mod_lt _ (by decide)
  | negSucc n => exact Nat.mod_lt _ (by decide)

theorem res15I_cast (z : ℤ) : (res15I z : ZMod 15) = (z : ZMod 15) := by
  cases z with
  | ofNat n =>
    change ((n % 15 : ℕ) : ZMod 15) = _
    rw [ZMod.natCast_mod]
    simp
  | negSucc n =>
    change (((15 - (n + 1) % 15) % 15 : ℕ) : ZMod 15) = _
    have hl : (n + 1) % 15 ≤ 15 := (Nat.mod_lt _ (by decide)).le
    have h15 : ((15 : ℕ) : ZMod 15) = 0 := rfl
    rw [ZMod.natCast_mod, Nat.cast_sub hl, ZMod.natCast_mod, Int.cast_negSucc, h15, zero_sub]

theorem lgetI_eq (l : List ℤ) (k : ℕ) : lgetI l k = l.getD k 0 := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change lgetI l k = _
      rw [ih]
      rfl

theorem aIdxT_eq : ∀ i < 24, ∀ j < 24, aIdxT i j = Native.aIdx i j := by decide +kernel

theorem aIdx_lt : ∀ i < 24, ∀ j < 24, Native.aIdx i j < 300 := by decide +kernel

theorem res15_ofATab (tab : Array ℤ) (k : ℕ) :
    res15 (ofATab tab) k = if k < 300 then ((tab[k]! : ℤ) : ZMod 15) else 0 := by
  unfold res15 ofATab
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, pow_zero, mul_one]
  by_cases hk : k < 196884
  · simp only [hk, dite_eq_left]
    split_ifs <;> simp
  · have h3 : ¬ k < 300 := by omega
    simp [hk, h3]

theorem lgetI_toList (tab : Array ℤ) (k : ℕ) : lgetI tab.toList k = tab[k]! := by
  rw [lgetI_eq]
  simp only [List.getD_eq_getElem?_getD, Array.getElem!_eq_getD, Array.getD, Array.getElem?_toList]
  by_cases hk : k < tab.size <;> simp [hk]

theorem testBit_one (y : ℕ) : (1 : ℕ).testBit y = decide (y = 0) := by
  have e : (1 : ℕ) = 2 ^ 0 := rfl
  rw [e, Nat.testBit_two_pow]
  simp [eq_comm]

theorem resP_low {S x : ℕ} (hx : x < 2 ^ S) (p : ℕ) :
    resP S x p = ((x.testBit p).toNat : ZMod 15) := by
  refine resP_of_bits (by cases x.testBit p <;> decide) fun b hb => ?_
  rcases b with _ | b
  · rw [zero_mul, zero_add]
    cases x.testBit p <;> rfl
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right_of_le (Nat.le_mul_of_pos_left S (Nat.succ_pos b)))))]
    cases x.testBit p
    · rw [Bool.toNat_false, Nat.zero_testBit]
    · rw [Bool.toNat_true, testBit_one]
      simp

theorem ones_eq' (S : ℕ) : ones S = 2 ^ S - 1 := by
  change 1 <<< S - 1 = _
  rw [Nat.one_shiftLeft]

theorem testBit_ones' (S y : ℕ) : (ones S).testBit y = decide (y < S) := by
  rw [ones_eq', Nat.testBit_two_pow_sub_one]

theorem testBit_shl (x k y : ℕ) :
    (Nat.shiftLeft x k).testBit y = true ↔ k ≤ y ∧ x.testBit (y - k) = true := by
  change (x <<< k).testBit y = true ↔ _
  rw [Nat.testBit_shiftLeft]
  simp

@[expose] noncomputable def oddBlk : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun t a => Nat.lor a (Nat.shiftLeft (ones 24) (32 * t))) 2048

theorem oddBlk_eq : Nat.land (ones 65536) valW = oddBlk := by decide +kernel

theorem testBit_oddBlk (p : ℕ) : oddBlk.testBit p = true ↔ p < 65536 ∧ p % 32 < 24 := by
  unfold oddBlk
  rw [testBit_foldOr (fun t => Nat.shiftLeft (ones 24) (32 * t))]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, testBit_shl, testBit_ones',
    decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    omega
  · intro h
    exact ⟨p / 32, by omega, by omega, by omega⟩

theorem testBit_regOct (p : ℕ) : regOct.testBit p = true ↔ 65536 ≤ p ∧ p < 114112 := by
  change (Nat.shiftLeft (ones 48576) 65536).testBit p = true ↔ _
  rw [testBit_shl, testBit_ones', decide_eq_true_eq]
  omega

theorem upA_bits : ∀ x < 1024, upA.testBit x = decide (x / 32 < x % 32 ∧ x % 32 < 24) := by
  decide +kernel

theorem upA_shr : upA >>> 1024 = 0 := by decide +kernel

theorem testBit_upA_shl (c p : ℕ) : (Nat.shiftLeft upA c).testBit p = true ↔
    c ≤ p ∧ p - c < 1024 ∧ (p - c) / 32 < (p - c) % 32 ∧ (p - c) % 32 < 24 := by
  rw [testBit_shl]
  by_cases h : p - c < 1024
  · rw [upA_bits _ h, decide_eq_true_eq]
    omega
  · have e : p - c = 1024 + (p - c - 1024) := by omega
    rw [e, ← Nat.testBit_shiftRight, upA_shr, Nat.zero_testBit]
    simp only [Bool.false_eq_true, and_false, false_iff]
    omega

theorem testBit_validX (p : ℕ) : validX.testBit p = true ↔ (p < 65536 ∧ p % 32 < 24) ∨
    (65536 ≤ p ∧ p < 114112) ∨
    (114688 ≤ p ∧ p - 114688 < 1024 ∧ (p - 114688) / 32 < (p - 114688) % 32 ∧
      (p - 114688) % 32 < 24) ∨
    (115712 ≤ p ∧ p - 115712 < 1024 ∧ (p - 115712) / 32 < (p - 115712) % 32 ∧
      (p - 115712) % 32 < 24) := by
  have e : validX = Nat.lor (Nat.land (ones 65536) valW) (Nat.lor regOct
      (Nat.lor (Nat.shiftLeft upA 114688) (Nat.shiftLeft upA 115712))) := rfl
  rw [e, oddBlk_eq]
  simp only [lor_eq, Nat.testBit_or, Bool.or_eq_true, testBit_oddBlk, testBit_regOct,
    testBit_upA_shl]

theorem validX_lt : validX < 2 ^ SX :=
  Nat.lt_pow_two_of_testBit _ fun y hy => by
    rw [← Bool.not_eq_true, testBit_validX]
    change y ≥ 131072 at hy
    omega

theorem pairTab_ok : ∀ m < 276,
    (Native.pairTab ())[m]!.1 < (Native.pairTab ())[m]!.2 ∧ (Native.pairTab ())[m]!.2 < 24 := by
  decide +kernel

theorem pairTab_idx : ∀ i < 24, ∀ j < 24, i < j →
    Native.pairIdx i j < 276 ∧ (Native.pairTab ())[Native.pairIdx i j]! = (i, j) := by
  decide +kernel

theorem xposK_mem {q : ℕ} (hq : q < 98280) : validX.testBit (xposK q) = true := by
  rw [testBit_validX]
  unfold xposK
  split_ifs with h1 h2 h3
  · have := pairTab_ok (q / 2) (by omega)
    omega
  · have := pairTab_ok (q / 2) (by omega)
    omega
  · omega
  · omega

theorem xposK_of_mem {p : ℕ} (h : validX.testBit p = true) : ∃ q < 98280, xposK q = p := by
  rw [testBit_validX] at h
  rcases h with h | h | h | h
  · refine ⟨552 + 24 * (p / 32) + p % 32, by omega, ?_⟩
    unfold xposK
    split_ifs <;> omega
  · refine ⟨49704 + (p - 65536), by omega, ?_⟩
    unfold xposK
    split_ifs <;> omega
  · obtain ⟨hm, he⟩ := pairTab_idx ((p - 114688) / 32) (by omega) ((p - 114688) % 32) (by omega)
      (by omega)
    refine ⟨2 * Native.pairIdx ((p - 114688) / 32) ((p - 114688) % 32), by omega, ?_⟩
    unfold xposK
    rw [ite_eq_left (by omega), ite_eq_left (by omega), Nat.mul_div_cancel_left _ (by decide), he]
    omega
  · obtain ⟨hm, he⟩ := pairTab_idx ((p - 115712) / 32) (by omega) ((p - 115712) % 32) (by omega)
      (by omega)
    refine ⟨2 * Native.pairIdx ((p - 115712) / 32) ((p - 115712) % 32) + 1, by omega, ?_⟩
    unfold xposK
    have e2 : (2 * Native.pairIdx ((p - 115712) / 32) ((p - 115712) % 32) + 1) / 2 =
        Native.pairIdx ((p - 115712) / 32) ((p - 115712) % 32) := by omega
    rw [ite_eq_left (by omega), ite_eq_right (by omega), e2, he]
    omega

theorem res15_ofRange (lo hi k : ℕ) :
    res15 (ofRange lo hi) k = if lo ≤ k ∧ k < hi ∧ k < 196884 then 1 else 0 := by
  unfold res15 ofRange
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, pow_zero, mul_one]
  by_cases hk : k < 196884
  · simp only [hk, dite_true, Option.getD_some, and_true]
    split_ifs <;> simp
  · simp [hk]

theorem xposK_lt' {q : ℕ} (hq : q < 98280) : xposK q < SX := by
  by_contra h
  have := xposK_mem hq
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le validX_lt (Nat.pow_le_pow_right (by decide)
    (by omega)))] at this
  exact Bool.false_ne_true this

theorem pairTab_idx2 : ∀ m < 276,
    Native.pairIdx (Native.pairTab ())[m]!.1 (Native.pairTab ())[m]!.2 = m := by
  decide +kernel

theorem xposK_inj {q q' : ℕ} (hq : q < 98280) (hq' : q' < 98280) (e : xposK q = xposK q') :
    q = q' := by
  unfold xposK at e
  rcases Nat.lt_or_ge q 552 with h1 | h1 <;> rcases Nat.lt_or_ge q' 552 with h1' | h1'
  · have t1 := pairTab_ok (q / 2) (by omega)
    have t2 := pairTab_ok (q' / 2) (by omega)
    have ha : (Native.pairTab ())[q / 2]!.1 = (Native.pairTab ())[q' / 2]!.1 ∧
        (Native.pairTab ())[q / 2]!.2 = (Native.pairTab ())[q' / 2]!.2 ∧ q % 2 = q' % 2 := by
      split_ifs at e <;> omega
    have i1 := pairTab_idx2 (q / 2) (by omega)
    have i2 := pairTab_idx2 (q' / 2) (by omega)
    rw [ha.1, ha.2.1, i2] at i1
    omega
  · have t1 := pairTab_ok (q / 2) (by omega)
    split_ifs at e <;> omega
  · have t2 := pairTab_ok (q' / 2) (by omega)
    split_ifs at e <;> omega
  · split_ifs at e <;> omega

end InitAux

open InitAux in
set_option maxRecDepth 100000 in
theorem aInit_sound (tab : Array Int) (s : St) (h : aInitOK tab s = true) : Rep (ofATab tab) s := by
  obtain ⟨f, X, A, W⟩ := s
  change andB f (andB (Nat.beq X 0) (andB (Nat.beq W 0) (Nat.beq A (aPlanes tab.toList)))) =
    true at h
  have hb : ∀ a b : Bool, andB a b = (a && b) := fun a b => by cases a <;> rfl
  simp only [hb, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨-, rfl, rfl, rfl⟩ := h
  have SAe : SA = 1024 := rfl
  have hA : ∀ y, (aPlanes tab.toList).testBit y = true ↔ ∃ i < 24, ∃ j < 24, ∃ b < 4,
      y = 32 * i + j + b * 1024 ∧
        (res15I (lgetI tab.toList (aIdxT i j))).testBit b = true := by
    intro y
    have e : aPlanes tab.toList = Nat.rec (motive := fun _ => ℕ) 0 (fun i a => Nat.rec
        (motive := fun _ => ℕ) a (fun j a2 => Nat.lor a2
          (put SA 4 (res15I (lgetI tab.toList (aIdxT i j))) (32 * i + j))) 24) 24 := rfl
    rw [e, testBit_foldOr2]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, testBit_put, SAe]
  have hA0 : ∀ y, (∀ i < 24, ∀ j < 24, ∀ b < 4, y ≠ 32 * i + j + b * 1024) →
      (aPlanes tab.toList).testBit y = false := by
    intro y hy
    rw [← Bool.not_eq_true, hA]
    rintro ⟨i, hi, j, hj, b, hb, rfl, -⟩
    exact hy i hi j hj b hb rfl
  refine ⟨fun q hq => ?_, fun p hp _ => resP_zero _ _, Nat.two_pow_pos _, fun i hi j hj => ?_,
    fun p hp hq => ?_, ?_, fun r hr j hj => ?_, fun p hp _ => resP_zero _ _, Nat.two_pow_pos _⟩
  · rw [resP_zero, res15_ofATab, ite_eq_right (by omega)]
  · rw [res15_ofATab, ite_eq_left (aIdx_lt i hi j hj), ← lgetI_toList, ← aIdxT_eq i hi j hj,
      ← res15I_cast]
    refine resP_of_bits (by have := res15I_lt (lgetI tab.toList (aIdxT i j)); omega) fun b hb => ?_
    rw [Bool.eq_iff_iff, hA, SAe]
    constructor
    · rintro ⟨i', hi', j', hj', b', hb', e, h⟩
      obtain ⟨rfl, rfl, rfl⟩ : i' = i ∧ j' = j ∧ b' = b := by omega
      exact h
    · exact fun h => ⟨i, hi, j, hj, b, hb, Nat.add_comm _ _, h⟩
  · rw [SAe] at hp
    refine (resP_of_bits (r := 0) (by decide) fun b hb => ?_).trans (by simp)
    rw [Nat.zero_testBit, SAe]
    exact hA0 _ fun i hi j hj b' hb' e => by omega
  · refine Nat.lt_pow_two_of_testBit _ fun y hy => hA0 y fun i hi j hj b hb e => ?_
    rw [SAe] at hy
    omega
  · rw [resP_zero, res15_ofATab, ite_eq_right (by omega)]

open InitAux in
set_option maxRecDepth 100000 in
theorem rangeInit_sound (lo hi : ℕ) (s : St) (h : rangeInitOK lo hi s = true) : Rep (ofRange lo hi) s := by
  obtain ⟨f, X, A, W⟩ := s
  have hb : ∀ a b : Bool, andB a b = (a && b) := fun a b => by cases a <;> rfl
  have ho : ∀ a b : Bool, CFSG.KC.orB a b = (a || b) := fun a b => by cases a <;> rfl
  change CFSG.KC.orB (andB (Nat.beq lo 300) (andB (Nat.beq hi 98580) (andB f
      (andB (Nat.beq X validX) (andB (Nat.beq A 0) (Nat.beq W 0))))))
    (andB (Nat.beq lo 98580) (andB (Nat.beq hi 98581) (andB f (andB (Nat.beq X 0)
      (andB (Nat.beq A 0) (Nat.beq W 1)))))) = true at h
  simp only [hb, ho, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  have hA : ∀ lo hi, 300 ≤ lo → ∀ i < 24, ∀ j < 24,
      resP SA 0 (32 * i + j) = res15 (ofRange lo hi) (Native.aIdx i j) :=
    fun lo hi hl i hi j hj => by
      rw [resP_zero, res15_ofRange, ite_eq_right]
      have := aIdx_lt i hi j hj
      omega
  have h4 : 2 ^ SX ≤ 2 ^ (4 * SX) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by decide))
  rcases h with ⟨rfl, rfl, -, rfl, rfl, rfl⟩ | ⟨rfl, rfl, -, rfl, rfl, rfl⟩
  · have hX4 : validX < 2 ^ (4 * SX) := lt_of_lt_of_le validX_lt h4
    refine ⟨fun q hq => ?_, fun p hp hq => ?_, by convert hX4 using 1, hA _ _ le_rfl,
      fun p _ _ => resP_zero _ _, Nat.two_pow_pos _, fun r hr j hj => ?_,
      fun p _ _ => resP_zero _ _, Nat.two_pow_pos _⟩
    · rw [resP_low validX_lt, xposK_mem hq, res15_ofRange, ite_eq_left (by omega)]
      rfl
    · have hf : validX.testBit p = false := by
        rw [← Bool.not_eq_true]
        intro h
        obtain ⟨q, hq', e⟩ := xposK_of_mem h
        exact hq q hq' e
      rw [resP_low validX_lt, hf]
      rfl
    · rw [resP_zero, res15_ofRange, ite_eq_right (by omega)]
  · have h1 : (1 : ℕ) < 2 ^ SX := Nat.one_lt_two_pow (by decide)
    refine ⟨fun q hq => ?_, fun p _ _ => resP_zero _ _, Nat.two_pow_pos _,
      hA _ _ (by decide), fun p _ _ => resP_zero _ _, Nat.two_pow_pos _, fun r hr j hj => ?_,
      fun p hp hq => ?_, lt_of_lt_of_le h1 h4⟩
    · rw [resP_zero, res15_ofRange, ite_eq_right (by omega)]
    · rw [resP_low h1, testBit_one, res15_ofRange]
      by_cases e : 32 * r + j = 0
      · rw [ite_eq_left (by omega), e]
        rfl
      · rw [ite_eq_right (by omega), decide_eq_false e]
        rfl
    · rw [resP_low h1, testBit_one]
      have e : p ≠ 0 := by omega
      simp [e]

end CFSG.KC.KDense

end
