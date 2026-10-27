module

public import Certificates.Data.Kernel.Co1Nine.Defs
public import CFSG.Sporadic.Co1Patterson.IndexNineInputs

public section

namespace CFSG.KC.Co1Nine

open CFSG.Sporadic.Co1Patterson.TwistNative CFSG.Sporadic.Co1Patterson.IndexNine

@[expose] noncomputable def unkey (k : Nat) : List Nat := (List.range 8).map (byteK k)

theorem byteK_eq (k i : Nat) : byteK k i = k / 256 ^ i % 256 := by
  change (k >>> (8 * i)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem letN_eq (y : Nat) (k : Nat → Nat) : letN y k = k y := by
  cases y <;> rfl

theorem bitN_eq (v i : Nat) : bitN v i = if v.testBit i then 1 else 0 := by
  have h : bitN v i = v / 2 ^ i % 2 := by
    change (v >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ i) with h0 | h1
  · simp [h0]
  · simp [h1]

theorem byteK_lt (k i : Nat) : byteK k i < 256 := by
  change (k >>> (8 * i)) &&& 255 < 256
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem unkey_getD {k i : Nat} (hi : i < 8) : (unkey k).getD i 0 = byteK k i := by
  rw [unkey, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem capK_aux (k v : Nat) : ∀ n ≤ 8,
    Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.xor acc (Nat.mul (bitN v i) (byteK k i))) n =
    (List.range n).foldl (fun acc i => if v.testBit i then acc ^^^ (unkey k).getD i 0 else acc) 0
  | 0, _ => rfl
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, ← capK_aux k v n (by omega)]
    change Nat.xor _ (Nat.mul (bitN v n) (byteK k n)) = _
    rw [List.foldl_cons, List.foldl_nil, unkey_getD (by omega), bitN_eq]
    cases v.testBit n
    · change _ ^^^ 0 * _ = _
      simp
    · change _ ^^^ 1 * _ = _
      simp

theorem capK_eq (k v : Nat) : capK k v = colsApply (unkey k) v :=
  capK_aux k v 8 le_rfl

theorem capK_lt (k v : Nat) : capK k v < 256 := by
  have h : ∀ n ≤ 8, Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.xor acc (Nat.mul (bitN v i) (byteK k i))) n < 2 ^ 8 := by
    intro n hn
    induction n with
    | zero => norm_num
    | succ n ih =>
      change Nat.xor _ (Nat.mul (bitN v n) (byteK k n)) < _
      refine Nat.xor_lt_two_pow (ih (by omega)) ?_
      rw [bitN_eq]
      split
      · simpa using byteK_lt k n
      · simp
  exact h 8 le_rfl

theorem mulC_aux (c : Nat → Nat) (hc : ∀ i, c i < 256) : ∀ n,
    Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft (c i) (Nat.mul 8 i))) n =
    Nat.ofDigits 256 ((List.range n).map c) ∧
    Nat.ofDigits 256 ((List.range n).map c) < 256 ^ n
  | 0 => ⟨rfl, by simp⟩
  | n + 1 => by
    obtain ⟨ih, hlt⟩ := mulC_aux c hc n
    have hlt' : Nat.ofDigits 256 ((List.range n).map c) < 2 ^ (8 * n) := by
      rwa [pow_mul]
    have hsum : Nat.ofDigits 256 ((List.range (n + 1)).map c) =
        Nat.ofDigits 256 ((List.range n).map c) + 256 ^ n * c n := by
      rw [List.range_succ, List.map_append, Nat.ofDigits_append, List.length_map,
        List.length_range]
      simp [Nat.ofDigits]
    refine ⟨?_, ?_⟩
    · change Nat.lor _ (Nat.shiftLeft (c n) (8 * n)) = _
      rw [ih, hsum]
      change _ ||| c n <<< (8 * n) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt', Nat.shiftLeft_eq, pow_mul]
      norm_num
      ring
    · rw [hsum, pow_succ]
      have := hc n
      nlinarith

theorem mulC_eq (a b : Nat) : mulC a b = co1RowsKeyC (colsMul (unkey a) (unkey b)) := by
  have hm : colsMul (unkey a) (unkey b) = (List.range 8).map fun i => capK a (byteK b i) := by
    unfold colsMul
    refine List.map_congr_left fun i hi => ?_
    rw [unkey_getD (List.mem_range.1 hi), capK_eq]
  rw [hm, co1RowsKeyC, List.take_of_length_le (by simp)]
  exact (mulC_aux (fun i => capK a (byteK b i)) (fun i => capK_lt _ _) 8).1

theorem unkey_key {m : List Nat} (hm : m.length = 8) (hlt : ∀ x ∈ m, x < 256) :
    unkey (co1RowsKeyC m) = m := by
  match m, hm with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
    have h0 := hlt a0 (by simp)
    have h1 := hlt a1 (by simp)
    have h2 := hlt a2 (by simp)
    have h3 := hlt a3 (by simp)
    have h4 := hlt a4 (by simp)
    have h5 := hlt a5 (by simp)
    have h6 := hlt a6 (by simp)
    have h7 := hlt a7 (by simp)
    simp only [unkey, List.range_succ, List.range_zero, List.nil_append, List.map_append,
      List.map_cons, List.map_nil, List.cons_append, byteK_eq, co1RowsKeyC, List.take,
      Nat.ofDigits, Nat.cast_id, Nat.reducePow]
    refine List.cons_eq_cons.2 ⟨by omega, List.cons_eq_cons.2 ⟨by omega,
      List.cons_eq_cons.2 ⟨by omega, List.cons_eq_cons.2 ⟨by omega, List.cons_eq_cons.2 ⟨by omega,
      List.cons_eq_cons.2 ⟨by omega, List.cons_eq_cons.2 ⟨by omega,
      List.cons_eq_cons.2 ⟨by omega, rfl⟩⟩⟩⟩⟩⟩⟩⟩

theorem stepF_eq (g : Nat) {p q : Nat} (hq : q < 256) :
    stepF g (p * 256 + q) = (co1FlagStepC (unkey g) (p, q)).1 * 256 +
      (co1FlagStepC (unkey g) (p, q)).2 := by
  have hp : (p * 256 + q) >>> 8 = p := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hq' : Nat.land (p * 256 + q) 255 = q := by
    change (p * 256 + q) &&& (2 ^ 8 - 1) = q
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e1 : Nat.shiftRight (p * 256 + q) 8 = p := hp
  unfold stepF
  rw [letN_eq, letN_eq, letN_eq]
  simp only [e1, hq', capK_eq]
  unfold co1FlagStepC
  generalize colsApply (unkey g) p = P
  generalize colsApply (unkey g) q = Q
  cases h : Nat.blt Q (Nat.xor Q P)
  · have h' : ¬ Q < (Q ^^^ P) := fun h2 => by
      rw [show Nat.xor Q P = Q ^^^ P from rfl, Nat.blt_eq.mpr h2] at h
      cases h
    simp only [h', if_false]
    rfl
  · have h' : Q < (Q ^^^ P) := Nat.blt_eq.mp h
    simp only [h', if_true]
    rfl

end CFSG.KC.Co1Nine

end
