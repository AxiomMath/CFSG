module

public import Certificates.Data.Kernel.G2Three.Defs
public import CFSG.Certificates.Kernel.G2Three.DecodePairs
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.G2Three

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.KD.G2Three

theorem digit_char {d : ℕ} (hd : d < 10) : Char.ofNat (48 + d) = Nat.digitChar d := by
  rw [← Nat.toNat_digitChar_of_lt_ten hd, Char.ofNat_toNat]

theorem digsF_small {f n : ℕ} (acc : List Char) (hn : n < 10) :
    digsF (f + 1) n acc = Nat.toDigits 10 n ++ acc := by
  have hb : Nat.blt n 10 = true := Nat.blt_eq.mpr hn
  rw [digsF, hb, cond_true, Nat.toDigits_of_lt_base hn]
  exact congrArg (· :: acc) (digit_char hn)

theorem digsF_eq (f : ℕ) :
    ∀ n acc, n < 10 ^ (f + 1) → digsF (f + 1) n acc = Nat.toDigits 10 n ++ acc := by
  induction f with
  | zero =>
    intro n acc h
    exact digsF_small acc (by simpa using h)
  | succ f ih =>
    intro n acc h
    by_cases hn : n < 10
    · exact digsF_small acc hn
    · have hb : Nat.blt n 10 = false := by
        cases hq : Nat.blt n 10
        · rfl
        · exact absurd (Nat.blt_eq.mp hq) hn
      rw [digsF, hb, cond_false, Nat.toDigits_eq_if (by decide), if_neg hn, List.append_assoc,
        List.singleton_append]
      have h' : n / 10 < 10 ^ (f + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by decide), ← Nat.pow_succ]
        exact h
      rw [← digit_char (Nat.mod_lt n (by decide : 10 > 0))]
      exact ih (n / 10) _ h'

theorem digs_eq {n : ℕ} (hn : n < 10 ^ 20) : digs n = Nat.toDigits 10 n := by
  have := digsF_eq 19 n [] hn
  rw [List.append_nil] at this
  exact this

theorem digs_digit {n : ℕ} (hn : n < 10 ^ 20) {c : Char} (hc : c ∈ digs n) : c.isDigit = true := by
  rw [digs_eq hn] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

theorem not_mem_digs {n : ℕ} (hn : n < 10 ^ 20) {c : Char} (hc : c.isDigit = false) :
    c ∉ digs n := fun h => by
  rw [digs_digit hn h] at hc
  exact Bool.noConfusion hc

theorem piece_split {a b : ℕ} (ha : a < 10 ^ 20) (hb : b < 10 ^ 20) :
    (pieceChars a b).splitOn ',' = [digs a, digs b] := by
  have e : pieceChars a b = [','].intercalate [digs a, digs b] := by
    rw [List.intercalate_cons_cons, List.intercalate_singleton, pieceChars, List.append_assoc,
      List.singleton_append]
  rw [e]
  refine List.splitOn_intercalate ',' (fun l hl => ?_) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact not_mem_digs ha (by decide)
  · exact not_mem_digs hb (by decide)

theorem piece_facts {a b : ℕ} (ha : a < 10 ^ 20) (hb : b < 10 ^ 20) :
    pairOf (pieceChars a b) = some (a, b) ∧ pieceOK (pieceChars a b) = true ∧
      ';' ∉ pieceChars a b := by
  refine ⟨?_, ?_, ?_⟩
  · unfold pairOf
    rw [piece_split ha hb]
    simp only [digs_eq ha, digs_eq hb, Nat.ofDigitChars_ten_toDigits]
  · unfold pieceOK
    rw [piece_split ha hb]
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, fun c hc => digs_digit ha hc⟩, fun c hc => digs_digit hb hc⟩
    · rw [digs_eq ha]
      exact Nat.toDigits_ne_nil
    · rw [digs_eq hb]
      exact Nat.toDigits_ne_nil
  · intro h
    rw [pieceChars, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact not_mem_digs ha (by decide) h
    · exact absurd h (by decide)
    · exact not_mem_digs hb (by decide) h

theorem decodePairs_render {cs : List Char} {N : ℕ} {A B : ℕ → ℕ} (hN : 0 < N)
    (hAB : ∀ i < N, A i < 10 ^ 20 ∧ B i < 10 ^ 20)
    (h : (cs == [';'].intercalate ((List.range N).map fun i => pieceChars (A i) (B i))) = true) :
    decodePairs (String.ofList cs) = (List.range N).map fun i => (A i, B i) := by
  have e := beq_iff_eq.1 h
  have hx : ∀ l ∈ (List.range N).map (fun i => pieceChars (A i) (B i)), ';' ∉ l := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
    rw [List.mem_range] at hi
    exact (piece_facts (hAB i hi).1 (hAB i hi).2).2.2
  have hne : (List.range N).map (fun i => pieceChars (A i) (B i)) ≠ [] := by
    rw [Ne, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  have hsp : cs.splitOn ';' = (List.range N).map fun i => pieceChars (A i) (B i) := by
    rw [e]
    exact List.splitOn_intercalate ';' hx hne
  have hok : piecesOK cs = true := by
    unfold piecesOK
    rw [hsp, List.all_eq_true]
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
    rw [List.mem_range] at hi
    exact (piece_facts (hAB i hi).1 (hAB i hi).2).2.1
  rw [decodePairs_ofList hok, hsp, List.filterMap_map, ← List.filterMap_eq_map']
  refine List.filterMap_congr fun i hi => ?_
  rw [List.mem_range] at hi
  exact (piece_facts (hAB i hi).1 (hAB i hi).2).1

end CFSG.KC.G2Three

end
