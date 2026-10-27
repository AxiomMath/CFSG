module

public import Certificates.Data.Kernel.Fi22Nbr3153
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.Fi22Snd

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native

theorem foldr_range_add {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i a, f i a = a + g i) :
    ∀ m a, (List.range m).foldr f a = a + ∑ i ∈ Finset.range m, g i
  | 0, a => by simp
  | m + 1, a => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_range_add hf m,
      hf, Finset.sum_range_succ]
    omega

theorem foldN_add {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i a, f i a = a + g i) (m a : Nat) :
    foldN m f a = a + ∑ i ∈ Finset.range m, g i := by
  rw [CFSG.KC.Pack.foldN_eq]
  exact foldr_range_add hf m a

theorem lor_two_pow {B c : Nat} (hc : c < 2 ^ 64) (p : Nat) :
    (2 ^ 64 * B + c) ||| 2 ^ (64 + p) = 2 ^ 64 * (B ||| 2 ^ p) + c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hc, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow]
  by_cases hj : j < 64
  · rw [if_pos hj, if_pos hj]
    have : ¬ 64 + p = j := by omega
    simp [this]
  · rw [if_neg hj, if_neg hj, Nat.testBit_or, Nat.testBit_two_pow]
    have e : decide (64 + p = j) = decide (p = j - 64) := decide_eq_decide.2 (by omega)
    rw [e]

theorem maskFold_aux (h : Nat → Nat) {f : Nat → Nat → Nat}
    (hf : ∀ i a, f i a = (a ||| 2 ^ (64 + h i)) + 1) :
    ∀ m B c, c + m < 2 ^ 64 → ∃ B', (List.range m).foldr f (2 ^ 64 * B + c) =
      2 ^ 64 * B' + (c + m) ∧ ∀ q, B'.testBit q = (B.testBit q || decide (∃ i < m, h i = q))
  | 0, B, c, _ => ⟨B, by simp, fun q => by simp⟩
  | m + 1, B, c, hm => by
    obtain ⟨B', h1, h2⟩ := maskFold_aux h hf m (B ||| 2 ^ h m) (c + 1) (by omega)
    refine ⟨B', ?_, fun q => ?_⟩
    · rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, hf,
        lor_two_pow (by omega), Nat.add_assoc, h1]
      omega
    · rw [h2, Nat.testBit_or, Nat.testBit_two_pow]
      cases hb : B.testBit q
      · simp only [Bool.false_or]
        apply Bool.eq_iff_iff.2
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨m, by omega, rfl⟩
          · exact ⟨i, by omega, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact Or.inr ⟨i, hi, rfl⟩
          · exact Or.inl rfl
      · simp

theorem maskFold_testBit (h : Nat → Nat) {f : Nat → Nat → Nat}
    (hf : ∀ i a, f i a = (a ||| 2 ^ (64 + h i)) + 1) {m : Nat} (hm : m < 2 ^ 64) (q : Nat) :
    (foldN m f 0 >>> 64).testBit q = decide (∃ i < m, h i = q) := by
  obtain ⟨B', h1, h2⟩ := maskFold_aux h hf m 0 0 (by omega)
  simp only [Nat.mul_zero, Nat.zero_add] at h1
  rw [CFSG.KC.Pack.foldN_eq, h1, Nat.shiftRight_eq_div_pow, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt hm, Nat.add_zero, h2]
  simp

theorem rg_lt (r i : Nat) : rg r i < 65536 := by
  have : rg r i ≤ 65535 := Nat.and_le_right
  omega

theorem decodeRow_eq (d r : Nat) : decodeRow d r = (List.range d).map (rg r) := rfl

theorem rowsArr_get {n d x : Nat} {R : Nat → Nat} (hx : x < n) :
    (rowsArr n d R)[x]! = decodeRow d (R x) := by
  rw [rowsArr, getElem!_pos _ _ (by simpa using hx), Array.getElem_ofFn]

theorem maskK_testBit {d : Nat} (hd : d < 2 ^ 64) (r q : Nat) :
    (Nat.shiftRight (maskK d r) (nat_lit 64)).testBit q = decide (q ∈ decodeRow d r) := by
  have h := maskFold_testBit (rg r) (f := fun i a => Nat.add (Nat.lor a
    (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (rg r i)))) (nat_lit 1))
    (fun i a => by
      change (a ||| 1 <<< (64 + rg r i)) + 1 = _
      rw [Nat.one_shiftLeft]) hd q
  refine h.trans (decide_eq_decide.2 ?_)
  simp [decodeRow_eq]

theorem imgMaskK_testBit {d : Nat} (hd : d < 2 ^ 64) (g r q : Nat) :
    (Nat.shiftRight (imgMaskK d g r) (nat_lit 64)).testBit q =
      decide (∃ i < d, pg (nat_lit 12) (nat_lit 4095) g (rg r i) = q) :=
  maskFold_testBit (fun i => pg (nat_lit 12) (nat_lit 4095) g (rg r i))
    (f := fun i a => Nat.add (Nat.lor a (Nat.shiftLeft (nat_lit 1)
      (Nat.add (nat_lit 64) (pg (nat_lit 12) (nat_lit 4095) g (rg r i))))) (nat_lit 1))
    (fun i a => by
      change (a ||| 1 <<< (64 + pg 12 4095 g (rg r i))) + 1 = _
      rw [Nat.one_shiftLeft]) hd q

theorem spreadK_eq (d r : Nat) :
    spreadK d r = ∑ i ∈ Finset.range d, (2 ^ (128 + 48 * rg r i) + 1) := by
  have h := foldN_add (f := fun i a => Nat.add (Nat.add a (Nat.shiftLeft (nat_lit 1)
    (Nat.add (nat_lit 128) (Nat.mul (nat_lit 48) (rg r i))))) (nat_lit 1))
    (g := fun i => 2 ^ (128 + 48 * rg r i) + 1)
    (fun i a => by
      change a + 1 <<< (128 + 48 * rg r i) + 1 = _
      rw [Nat.one_shiftLeft]
      omega) d 0
  rw [Nat.zero_add] at h
  exact h

variable {n d x : Nat} {R M S : Nat → Nat}

theorem rowOK_facts (h : rowOK n d R M S x = true) :
    rg (R x) (d - 1) < n ∧ (∀ i < d - 1, rg (R x) i < rg (R x) (i + 1)) ∧
      Nat.shiftRight (maskK d (R x)) (nat_lit 64) = M x ∧ spreadK d (R x) + (x + 1) = S x + d := by
  unfold rowOK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h'⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h''⟩ := CFSG.KC.Pack.band_iff.1 h'
  obtain ⟨h3, h4⟩ := CFSG.KC.Pack.band_iff.1 h''
  exact ⟨Nat.le_of_ble_eq_true h1,
    fun i hi => Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec h2 i hi),
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem row_strict (h : rowOK n d R M S x = true) {i j : Nat} (hij : i < j) (hj : j < d) :
    rg (R x) i < rg (R x) j := by
  obtain ⟨-, h2, -⟩ := rowOK_facts h
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
    · exact lt_trans (ih hij (by omega)) (h2 j (by omega))
    · exact h2 i (by omega)

theorem row_lt (h : rowOK n d R M S x = true) {i : Nat} (hi : i < d) : rg (R x) i < n := by
  obtain ⟨h1, -⟩ := rowOK_facts h
  rcases Nat.lt_or_ge i (d - 1) with hi' | hi'
  · exact lt_trans (row_strict h hi' (by omega)) h1
  · obtain rfl : i = d - 1 := by omega
    exact h1

theorem row_d_le (h : rowOK n d R M S x = true) : d ≤ 65536 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · omega
  have key : ∀ i < d, i ≤ rg (R x) i := by
    intro i hi
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      exact Nat.succ_le_of_lt
        (lt_of_le_of_lt (ih (by omega)) (row_strict h (Nat.lt_succ_self i) hi))
  have h1 := key (d - 1) (by omega)
  have h2 := rg_lt (R x) (d - 1)
  omega

theorem row_d_lt (h : rowOK n d R M S x = true) : d < 2 ^ 64 :=
  lt_of_le_of_lt (row_d_le h) (by norm_num)

theorem row_pairwise (h : rowOK n d R M S x = true) : (decodeRow d (R x)).Pairwise (· < ·) := by
  rw [decodeRow_eq, List.pairwise_map]
  exact List.pairwise_lt_range.imp_of_mem fun _ hb hab => row_strict h hab (List.mem_range.1 hb)

theorem row_entry_lt (h : rowOK n d R M S x = true) {p : Nat} (hp : p ∈ decodeRow d (R x)) :
    p < n := by
  rw [decodeRow_eq, List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact row_lt h (List.mem_range.1 hi)

theorem row_length (d r : Nat) : (decodeRow d r).length = d := by
  rw [decodeRow_eq, List.length_map, List.length_range]

theorem row_mask (h : rowOK n d R M S x = true) (q : Nat) :
    (M x).testBit q = decide (q ∈ decodeRow d (R x)) := by
  obtain ⟨-, -, h3, -⟩ := rowOK_facts h
  rw [← h3]
  exact maskK_testBit (row_d_lt h) (R x) q

theorem row_spread (h : rowOK n d R M S x = true) :
    S x = x + 1 + ∑ i ∈ Finset.range d, 2 ^ (128 + 48 * rg (R x) i) := by
  obtain ⟨-, -, -, h4⟩ := rowOK_facts h
  rw [spreadK_eq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    Nat.mul_one] at h4
  omega

theorem beq_bit (y i : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight y i) (nat_lit 1)) (nat_lit 1) = y.testBit i := by
  have h : Nat.land (Nat.shiftRight y i) (nat_lit 1) = y / 2 ^ i % 2 := by
    change (y >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (y / 2 ^ i) with h0 | h1
  · rw [h0]
    rfl
  · rw [h1]
    rfl

private theorem bool_root {b c e : Bool}
    (h : Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (!e) true c)
      (Bool.rec (motive := fun _ => Bool) false e (!c)) b = true) :
    b = true ↔ (c = false ∧ e = true) := by
  revert h
  cases b <;> cases c <;> cases e <;> decide

private theorem beq_true_iff (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem rootOK_iff {Z i : Nat} (h : rootOK M Z i = true) :
    (M 0).testBit i = true ↔ (i ≠ 0 ∧ pg (nat_lit 12) (nat_lit 4095) Z i = i) := by
  unfold rootOK at h
  rw [beq_bit] at h
  refine (bool_root h).trans ?_
  rw [Bool.eq_false_iff, Ne, beq_true_iff, beq_true_iff]

theorem imgOK_facts {g : Nat} (h : imgOK n d g R M x = true) :
    pg (nat_lit 12) (nat_lit 4095) g x < n ∧
      Nat.shiftRight (imgMaskK d g (R x)) (nat_lit 64) =
        M (pg (nat_lit 12) (nat_lit 4095) g x) := by
  unfold imgOK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  rw [CFSG.KC.Pack.strictB_eq] at h2
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

private theorem mask12 : mask 12 = 4095 := by decide

theorem unpack12_get {P i : Nat} (hi : i < n) :
    (unpack n 12 P)[i]! = pg (nat_lit 12) (nat_lit 4095) P i := by
  rw [CFSG.KS.Raw.Orb.unpack_get hi, mask12]

theorem root_sound' {Z : Nat} (hrow : rowOK n d R M S 0 = true)
    (hr : ∀ i < n, rootOK M Z i = true) :
    decodeRow d (R 0) = (List.range n).filter fun i => i != 0 && (unpack n 12 Z)[i]! == i := by
  refine List.SortedLT.eq_of_mem_iff (row_pairwise hrow).sortedLT
    (List.pairwise_lt_range.filter _).sortedLT fun q => ?_
  rw [List.mem_filter, List.mem_range]
  constructor
  · intro hq
    have hqn := row_entry_lt hrow hq
    have hb : (M 0).testBit q = true := by
      rw [row_mask hrow]
      exact decide_eq_true hq
    obtain ⟨h1, h2⟩ := (rootOK_iff (hr q hqn)).1 hb
    refine ⟨hqn, ?_⟩
    rw [unpack12_get hqn, h2]
    simp [h1]
  · rintro ⟨hqn, hq⟩
    rw [unpack12_get hqn] at hq
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hq
    have hb := (rootOK_iff (hr q hqn)).2 hq
    rw [row_mask hrow] at hb
    exact of_decide_eq_true hb

theorem img_sound' {P : Nat} {g : Array Nat} (hrow : ∀ x < n, rowOK n d R M S x = true)
    (hg : g = unpack n 12 P) (himg : ∀ x < n, imgOK n d P R M x = true) :
    allLt n (fun x => (rowsArr n d R)[g[x]!]! == imgSorted g (rowsArr n d R)[x]!) = true := by
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro x hx
  rw [beq_iff_eq]
  subst hg
  obtain ⟨hy, hmask⟩ := imgOK_facts (himg x hx)
  rw [unpack12_get hx, rowsArr_get hy, rowsArr_get hx]
  set y := pg (nat_lit 12) (nat_lit 4095) P x with hy_def
  have hrx := hrow x hx
  have hry := hrow y hy
  symm
  refine List.Perm.eq_of_sortedLE List.sortedLE_mergeSort (row_pairwise hry).sortedLT.sortedLE ?_
  refine (List.mergeSort_perm _ _).trans ?_
  have hsub : decodeRow d (R y) ⊆ (decodeRow d (R x)).map fun p => (unpack n 12 P)[p]! := by
    intro q hq
    have hb : (M y).testBit q = true := by
      rw [row_mask hry]
      exact decide_eq_true hq
    rw [← hmask, imgMaskK_testBit (row_d_lt hrx)] at hb
    obtain ⟨i, hi, hiq⟩ := of_decide_eq_true hb
    rw [List.mem_map]
    refine ⟨rg (R x) i, ?_, ?_⟩
    · rw [decodeRow_eq]
      exact List.mem_map_of_mem (List.mem_range.2 hi)
    · rw [unpack12_get (row_lt hrx hi), hiq]
  have hperm := ((row_pairwise hry).nodup.subperm hsub).perm_of_length_le (by
    rw [List.length_map, row_length, row_length])
  exact hperm.symm

end CFSG.KC.Fi22Snd

end
