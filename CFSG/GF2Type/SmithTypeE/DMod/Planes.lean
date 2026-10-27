module

public import CFSG.GF2Type.SmithTypeE.DMod.V12

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

theorem xorComb_zero (B : Array ℕ) : xorComb B 0 = 0 := by
  simp [xorComb, Nat.zero_testBit, List.foldl_fixed]

theorem foldl_xor_testBit_split (f : ℕ → ℕ) (d e n : ℕ) :
    (List.range n).foldl (fun acc m => if (d ^^^ e).testBit m then acc ^^^ f m else acc) 0 =
      (List.range n).foldl (fun acc m => if d.testBit m then acc ^^^ f m else acc) 0 ^^^
        (List.range n).foldl (fun acc m => if e.testBit m then acc ^^^ f m else acc) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rw [Nat.testBit_xor]
    cases hd : d.testBit n <;> cases he : e.testBit n <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm, Nat.xor_self]

theorem xorComb_xor (B : Array ℕ) (d e : ℕ) : xorComb B (d ^^^ e) = xorComb B d ^^^ xorComb B e :=
  foldl_xor_testBit_split (fun m => B[m]!) d e 6

theorem xorComb_two_pow (B : Array ℕ) {m : ℕ} (hm : m < 6) : xorComb B (2 ^ m) = B[m]! := by
  unfold xorComb
  simp only [Nat.testBit_two_pow]
  interval_cases m <;> simp [List.range_succ]

theorem xorComb_lt {B : Array ℕ} (hB : ∀ m < 6, B[m]! < 4096) (d : ℕ) : xorComb B d < 4096 := by
  have key : ∀ n, n ≤ 6 → (List.range n).foldl
      (fun acc m => if d.testBit m then acc ^^^ B[m]! else acc) 0 < 2 ^ 12 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h0 := ih (by omega)
      have hb : B[n]! < 2 ^ 12 := by
        have := hB n (by omega)
        norm_num
        omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split_ifs
      · exact Nat.xor_lt_two_pow h0 hb
      · exact h0
  exact key 6 le_rfl

theorem coefOf_lt (P : Array ℕ) (x : ℕ) : coefOf P x < 64 := by
  unfold coefOf
  have key : ∀ n, n ≤ 6 → (List.range n).foldl
      (fun c m => if x.testBit P[m]! then c ||| 2 ^ m else c) 0 < 2 ^ 6 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h0 := ih (by omega)
      have hp : 2 ^ n < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split_ifs
      · exact Nat.or_lt_two_pow h0 hp
      · exact h0
  exact key 6 le_rfl

theorem memR_sound {B P : Array ℕ} {x : ℕ} (h : memR B P x = true) :
    ∃ d < 64, x = xorComb B d := by
  refine ⟨coefOf P x, coefOf_lt P x, ?_⟩
  have h' : (xorComb B (coefOf P x) == x) = true := h
  exact (beq_iff_eq.1 h').symm

@[expose] noncomputable def planeSpan (B : Array ℕ) : Submodule (ZMod 2) V12 :=
  Submodule.span (ZMod 2) (Set.range fun m : Fin 6 => dec12 B[m.val]!)

theorem dec12_foldl_mem_planeSpan_aux (B : Array ℕ) (d : ℕ) : ∀ n, n ≤ 6 →
    dec12 ((List.range n).foldl (fun acc m => if d.testBit m then acc ^^^ B[m]! else acc) 0) ∈
      planeSpan B := by
  intro n
  induction n with
  | zero =>
    intro _
    simpa [dec12_zero] using (planeSpan B).zero_mem
  | succ n ih =>
    intro hn
    have h0 := ih (by omega)
    have hgen : dec12 B[n]! ∈ planeSpan B :=
      Submodule.subset_span (Set.mem_range_self (⟨n, by omega⟩ : Fin 6))
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split_ifs
    · rw [dec12_xor]
      exact Submodule.add_mem _ h0 hgen
    · exact h0

theorem mem_planeSpan_iff {B : Array ℕ} {x : V12} :
    x ∈ planeSpan B ↔ ∃ d < 64, x = dec12 (xorComb B d) := by
  constructor
  · intro hx
    unfold planeSpan at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      refine ⟨2 ^ m.val, ?_, ?_⟩
      · have h6 : 2 ^ m.val < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) m.isLt
        exact h6.trans_eq (by norm_num)
      · rw [xorComb_two_pow B m.isLt]
    | zero => exact ⟨0, by norm_num, by rw [xorComb_zero, dec12_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, rfl⟩ := hx
      obtain ⟨e, he, rfl⟩ := hy
      refine ⟨d ^^^ e, ?_, ?_⟩
      · exact Nat.xor_lt_two_pow (n := 6) (show d < 2 ^ 6 from hd) (show e < 2 ^ 6 from he)
      · rw [xorComb_xor, dec12_xor]
    | smul c x _ hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
      · exact ⟨0, by norm_num, by rw [zero_smul, xorComb_zero, dec12_zero]⟩
      · exact ⟨d, hd, by rw [one_smul]⟩
  · rintro ⟨d, -, rfl⟩
    unfold xorComb
    exact dec12_foldl_mem_planeSpan_aux B d 6 le_rfl

theorem dec12_xorComb_mem_planeSpan (B : Array ℕ) (d : ℕ) : dec12 (xorComb B d) ∈ planeSpan B :=
  dec12_foldl_mem_planeSpan_aux B d 6 le_rfl

theorem dec12_mem_planeSpan_of_memR {B P : Array ℕ} {c : ℕ} (h : memR B P c = true) :
    dec12 c ∈ planeSpan B := by
  obtain ⟨d, hd, hc⟩ := memR_sound h
  rw [hc]
  exact mem_planeSpan_iff.2 ⟨d, hd, rfl⟩

theorem fst_dec12_eq_zero_iff (c : ℕ) : (dec12 c).1 = 0 ↔ ∀ i < 6, c.testBit i = false := by
  constructor
  · intro h i hi
    have h' : bit (c.testBit i) = bit false := congrFun h ⟨i, hi⟩
    exact bit_inj _ _ h'
  · intro h
    funext j
    have hj : c.testBit j.val = false := h j.val j.isLt
    show bit (c.testBit j.val) = bit false
    rw [hj]

theorem testBit_and_63 (c i : ℕ) : (c &&& 63).testBit i = (decide (i < 6) && c.testBit i) := by
  rw [Nat.testBit_and]
  by_cases hi : i < 6
  · have h63 : (63 : ℕ).testBit i = true := by
      have h := show ∀ j < 6, (63 : ℕ).testBit j = true by decide
      exact h i hi
    rw [h63, decide_eq_true hi, Bool.and_true, Bool.true_and]
  · have h63 : (63 : ℕ).testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : (63 : ℕ) < 2 ^ 6)
        (Nat.pow_le_pow_right (by norm_num) (by omega : 6 ≤ i)))
    rw [h63, decide_eq_false hi, Bool.and_false, Bool.false_and]

theorem testBit_mul_64_of_lt (d i : ℕ) (hi : i < 6) : (64 * d).testBit i = false := by
  rw [show (64 : ℕ) * d = d * 2 ^ 6 by ring, Nat.testBit_mul_two_pow,
    decide_eq_false (by omega : ¬ (6 ≤ i)), Bool.false_and]

theorem xorComb_fBasis_eq (d : ℕ) (hd : d < 64) : xorComb fBasis d = 64 * d := by
  have key : ∀ e : Fin 64, xorComb fBasis e.val = 64 * e.val := by decide
  exact key ⟨d, hd⟩

theorem mem_planeSpan_fBasis_iff {x : V12} : x ∈ planeSpan fBasis ↔ x.1 = 0 := by
  constructor
  · intro hx
    obtain ⟨d, hd, rfl⟩ := mem_planeSpan_iff.1 hx
    rw [xorComb_fBasis_eq d hd, fst_dec12_eq_zero_iff]
    intro i hi
    exact testBit_mul_64_of_lt d i hi
  · intro hx
    have hc0 : (dec12 (enc12 x)).1 = 0 := by
      rw [dec12_enc12]
      exact hx
    have hc : ∀ i < 6, (enc12 x).testBit i = false := (fst_dec12_eq_zero_iff _).1 hc0
    have hmod : enc12 x % 64 = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.testBit_mod_two_pow, Nat.zero_testBit]
      by_cases hi : i < 6
      · rw [decide_eq_true hi, Bool.true_and, hc i hi]
      · rw [decide_eq_false hi, Bool.false_and]
    have hlt : enc12 x < 4096 := enc12_lt x
    refine mem_planeSpan_iff.2 ⟨enc12 x / 64, by omega, ?_⟩
    have e : 64 * (enc12 x / 64) = enc12 x := by omega
    rw [xorComb_fBasis_eq (enc12 x / 64) (by omega), e, dec12_enc12]

end CFSG.GF2Type.SmithTypeE.DMod
